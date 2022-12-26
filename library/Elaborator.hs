{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes, ScopedTypeVariables #-}
-- | Typecheck and elaborate a program.
module Elaborator where



import CompileQuery
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map.Lazy as M
import GHC.Stack (HasCallStack)
import qualified Data.Typeable as Ty
import Data.Kind (Type)
import Data.Bifunctor (second)


-- for now, only do nonrecursive definitions via an implicit topo sort
elaborate :: TopLevel -> TopLevel
elaborate tl = tl { defs = defs' }
  where
    elabLang l = either error id $ runExcept (runReaderT (tcLang l) topLevel)
    defs' = M.map (second elabLang) (defs tl)
    topLevel = M.map (lTy . snd) $ M.mapKeysMonotonic unSource defs'

typeRep :: forall (a::Type). Ty.Typeable a => Ty.TypeRep
typeRep = Ty.typeOf @a undefined


type Env = M.Map Var ExprType
type Error = String
type M = ReaderT Env (Except Error)

nTy :: HasCallStack => Expr -> ExprType
nTy (HasEType _ ty) = ty
nTy a = error ("nTy: not a HasEType\n" <> prettyS a)

lTy :: HasCallStack => Lang -> ExprType
lTy (OpLang (HasType _ ty)) = ty
lTy l = error ("lTy: not a HasEType\n" <> prettyS l)

-- Rewrite it into a normal form with an HasEType on top
tcThunk :: Thunk -> M ExprType
tcThunk (Thunk sym _) = do
   thunkOut <- lookupVar (unSource sym)
   pure (ListTy thunkOut)
tcExpr :: Expr -> M Expr
tcExpr e@(HasEType {}) = pure e
tcExpr (Ref r) = setEType (Ref r) <$> lookupVar r
tcExpr (AThunk thunk) = do
   thunkTy <- tcThunk thunk
   pure $ setEType (AThunk thunk) thunkTy
tcExpr (Proj i e) = do
   e' <- tcExpr e
   case nTy e' of
      TupleTyp tys -> pure $ setEType (Proj i e') (tys !! i)
      _ -> throwError "tcExpr: Proj on non-record"
tcExpr Unit = pure $ setEType Unit (TupleTyp [])
tcExpr (Tuple es) = do
   es' <- traverse tcExpr es
   pure $ setEType (Tuple es') (TupleTyp (map nTy es'))
tcExpr (BOp op a b) = do
  a' <- tcExpr a
  b' <- tcExpr b
  case op of
    Eql -> pure $ setEType (BOp op a' b') (EBase (typeRep @Bool))
tcExpr (Aggr op thunk) = do
  thunkTy <- tcThunk thunk
  outTy <- checkOp op thunkTy
  pure $ setEType (Aggr op thunk) outTy
tcExpr (Pack args) = do
   argTys <- traverse lookupVar args
   pure $ setEType (Pack args) (TupleTyp argTys)
tcExpr (AggrNested {}) = error "tcExpr: Not Unnested before typechecking"
tcExpr (Nest {}) = error "tcExpr: Not Unnested before typechecking"

setEType :: Expr -> ExprType -> Expr
setEType (HasEType e _) ty = HasEType e ty
setEType l ty = HasEType l ty

setType :: Lang -> ExprType -> Lang
setType (OpLang (HasType op _)) ty = OpLang (HasType op ty)
setType l ty = OpLang (HasType l ty)

tcLang :: Lang -> M Lang
tcLang (Bind generator v body) = do
   generator' <- tcLang generator
   ty <- case lTy generator' of
     ListTy ty -> pure ty
     o -> throwError $ "tcLang: Bind on non-list: " <> prettyS o <> "\n" <> prettyS generator'
   body' <- local (M.insert v ty) (tcLang body)
   pure $ setType (Bind generator' v body') (lTy body')
tcLang (Return expr) = do
   expr' <- tcExpr expr
   pure $ setType (Return expr') (ListTy $ nTy expr')
tcLang (Filter expr body) = do
   expr' <- tcExpr expr
   assert (nTy expr' == EBase (typeRep @Bool)) "tcLang: Filter on non-bool"
   body' <- tcLang body
   pure $ setType (Filter expr' body') (lTy body')
tcLang (LRef r) = do
   ty <- lookupVar r
   pure $ setType (LRef r) ty
tcLang (OpLang l) = OpLang <$> tcOpLang l
tcLang (AsyncBind {}) = error "tcLang: Not Unnested before typechecking"

tcOpLang :: OpLang -> M OpLang
tcOpLang w@(HasType {})= pure w
tcOpLang (Opaque s) = throwError ("Untyped opaque: " <> show s)
tcOpLang (Union a b) = do
   a' <- tcLang a
   b' <- tcLang b
   unify (lTy a') (lTy b')
   pure $ HasType (OpLang $ Union a' b') (lTy a')
tcOpLang (Unpack l vs body) = do
  l' <- tcLang l
  case lTy l' of
    TupleTyp tys -> do
      body' <- local (M.union (M.fromList (zipStrict vs tys))) (tcLang body)
      pure $ HasType (OpLang $ Unpack l' vs body') (lTy body')
    _ -> throwError ("tcOpLang: Unpack on non-record: " <> prettyS l')
tcOpLang (Lookup source args v body) = do
   sourceTy <- lookupVar (unSource source)
   body' <- local (M.insert v (ListTy sourceTy)) (tcLang body)
   pure $ HasType (OpLang $ Lookup source args v body') (lTy body')
tcOpLang (Group op body) = do
  body' <- tcLang body
  keyTy <- mapTyKey (lTy body')
  outTy <- checkOp op =<< mapTyVal (lTy body')
  pure $ HasType (OpLang $ Group op body') (ListTy $ TupleTyp [keyTy, outTy])
  where

    mapTyKey :: ExprType -> M ExprType
    mapTyKey (ListTy (TupleTyp [a,_])) = pure a
    mapTyKey ty = throwError ("mapTyVal: not a key-value pair: " <> show ty)
    mapTyVal :: ExprType -> M ExprType
    mapTyVal (ListTy (TupleTyp [_,b])) = pure $ ListTy b
    mapTyVal ty = throwError ("mapTyVal: not a key-value pair: " <> show ty)

checkOp :: AggrOp -> ExprType -> M ExprType
checkOp op ty = do
  unify (ListTy (inpTy op)) ty 
  pure (outTy op)
  where
    inpTy _ = EBase (typeRep @Int)
    outTy _ = EBase (typeRep @Int)

zipStrict :: [a] -> [b] -> [(a, b)]
zipStrict [] [] = []
zipStrict (a:as) (b:bs) = (a, b) : zipStrict as bs
zipStrict _ _ = error "zipStrict: lists of different length"

unify :: ExprType -> ExprType -> M ()
unify l r = assert (l == r) ("tcOpLang: Union on different types" <> prettyS l <> prettyS r)




assert :: (MonadError s m) => Bool -> s -> m ()
assert True _ = pure ()
assert False msg = throwError msg

-- tcExpr (Nest es) = do

lookupVar :: HasCallStack => Var -> M ExprType
lookupVar v = asks (M.lookup v) >>= \case
  Just ty -> pure ty
  Nothing -> throwError $ "Variable not in scope: " ++ show v
