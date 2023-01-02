{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes, ScopedTypeVariables #-}
-- | Typecheck and elaborate a program.
module Elaborator where



import CompileQuery
import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map.Lazy as M
import GHC.Stack (HasCallStack, prettyCallStack, callStack)
import qualified Data.Typeable as Ty
import Data.Kind (Type)
import Data.Functor (($>))
import Control.Monad.State.Strict
import Data.Function ((&))
import Data.Foldable (traverse_)
import Data.Data (Data)
import OpenRec
import Debug.Trace (trace, traceM)
import Data.Maybe (fromMaybe)

-- for now, only do nonrecursive definitions via an implicit topo sort
elaborate :: TopLevel -> TopLevel
elaborate tl = tl { defs = defs' }
  where
    elabLang (vars, l) = do
      -- traceM $ "elaborating " ++ show vars
      out <- freshVars vars (\_ -> tcLang l)
      pure (vars, out)
    freshVars = go []
      where
        go acc (v:vs) m = do
          v' <- freshUVar
          localType v v' (go (acc <> [v']) vs m)
        go acc [] m = m acc
    defs' = M.fromList $ either error id $ runExcept (runReaderT (evalStateT (defs_ >>= setUVars) emptyUnificationEnv) topLevel)
    defs_ = do
        let topVars = M.keys (defs tl)
        freshVars (map unSource topVars) $ \bound -> do
            ls <- traverse (overSecond elabLang) $ M.toList $ defs tl
            topTys <- traverse (setUVars . lTy . snd . snd) ls
            let topBound = zip bound topTys
            -- traceM $ "topBound: " ++ prettyS topBound
            -- traceM $ "env: " ++ prettyS (M.toList env)
            traverse_ (uncurry unify) topBound
            -- env <- traverse (overSecond setUVars) . M.toList =<< gets uEnv
            -- traceM $ "env': " ++ prettyS env
            pure ls
    topLevel = mempty

fillUVars :: ExprType -> M ExprType
fillUVars (TupleTyp t) = TupleTyp <$> traverse fillUVars t
fillUVars (ListTy t) = ListTy <$> fillUVars t
fillUVars (ThunkTy t arg) = ThunkTy t <$> fillUVars arg
fillUVars (UnificationVar v) = do
    env <- gets uEnv
    case M.lookup v env of
        Nothing -> pure $ UnificationVar v
        Just t -> fillUVars t
fillUVars t = pure t


setUVars :: Data a => a -> M a
setUVars = runT (
    tryTransM_ ( \(a::ExprType) -> Just $ fillUVars a) ||| recurse)

overSecond :: Monad m => (b -> m b) -> (a,b) -> m (a,b)
overSecond f (a,b) = (a,) <$> f b

localType :: Var -> ExprType -> M b -> M b
localType v ty = local (M.insert v ty)

typeRep :: forall (a::Type). Ty.Typeable a => Ty.TypeRep
typeRep = Ty.typeOf @a undefined


type Env = M.Map Var ExprType
type Error = String
type UVar = Int
data UnificationEnv = UnificationEnv { uEnv :: M.Map UVar ExprType, uNext :: UVar }
emptyUnificationEnv :: UnificationEnv
emptyUnificationEnv = UnificationEnv M.empty 0
type M = StateT UnificationEnv (ReaderT Env (Except Error))

nTy :: HasCallStack => Expr -> ExprType
nTy (HasEType _ _ ty) = ty
nTy a = error ("nTy: not a HasEType\n" <> prettyS a)

lTy :: HasCallStack => Lang -> ExprType
lTy (OpLang (HasType _ _ ty)) = ty
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
tcExpr (Proj i tot e) = do
   e' <- tcExpr e
   case nTy e' of
      TupleTyp tys -> pure $ setEType (Proj i tot e') (tys !! i)
      uv@UnificationVar {} -> do
         v <- replicateM tot freshUVar
         unify uv (TupleTyp v)
         pure $ setEType (Proj i tot e) (v !! i)
      _ -> throwError ("tcExpr: Proj on non-record" <> show e)
tcExpr Unit = pure $ setEType Unit (TupleTyp [])
tcExpr (Tuple es) = do
   es' <- traverse tcExpr es
   pure $ setEType (Tuple es') (TupleTyp (map nTy es'))
tcExpr (BOp op a b) = do
  a' <- tcExpr a
  b' <- tcExpr b
  case op of
    Eql -> do
        unify (nTy a') (nTy b') 
        pure $ setEType (BOp op a' b') (EBase (typeRep @Bool))
tcExpr (Aggr op thunk) = do
  thunkTy <- tcThunk thunk
  outTy <- checkOp op thunkTy
  pure $ setEType (Aggr op thunk) outTy
tcExpr (Pack args) = do
   argTys <- traverse lookupVar args
   pure $ setEType (Pack args) (TupleTyp argTys)
tcExpr (AggrNested op t) = do
  sourceTy <- tcLang t
  oTy <- checkOp op (lTy sourceTy)
  pure $ setEType (AggrNested op t) oTy
tcExpr (Nest n) = do
  sourceTy <- tcLang n
  pure $ setEType (Nest n) (ListTy (lTy sourceTy))
tcExpr l@(Lookup source _) = do
   sourceTy <- lookupVar (unSource source)
   pure $ hasEType l sourceTy

hasEType :: Expr -> ExprType -> Expr
hasEType = HasEType Inferred
hasType :: Lang -> ExprType -> Lang
hasType l ty = OpLang (HasType Inferred l ty)

setEType :: Expr -> ExprType -> Expr
setEType (HasEType r e _) ty = HasEType r e ty
setEType l ty = hasEType l ty

setType :: Lang -> ExprType -> M Lang
setType (OpLang (HasType r op ty')) ty = unify ty' ty $> OpLang (HasType r op ty)
setType l ty = pure (hasType l ty)

tcLang :: Lang -> M Lang
tcLang (Bind generator v body) = do
   generator' <- tcLang generator
   ty <- case lTy generator' of
     ListTy ty -> pure ty
     ov@UnificationVar {} -> do
       v' <- freshUVar
       unify ov (ListTy v')
       pure v'
     o -> throwError $ "tcLang: Bind on non-list: " <> prettyS o <> "\n" <> prettyS generator'
   body' <- local (M.insert v ty) (tcLang body)
   setType (Bind generator' v body') (lTy body')
tcLang (Return expr) = do
   expr' <- tcExpr expr
   setType (Return expr') (ListTy $ nTy expr')
tcLang (Filter expr body) = do
   expr' <- tcExpr expr
   assert (nTy expr' == EBase (typeRep @Bool)) "tcLang: Filter on non-bool"
   body' <- tcLang body
   setType (Filter expr' body') (lTy body')
tcLang (LRef r) = do
   ty <- lookupVar r
   setType (LRef r) ty
tcLang (OpLang l) = OpLang <$> tcOpLang l
tcLang (AsyncBind {}) = error "tcLang: Not Unnested before typechecking"

tcOpLang :: OpLang -> M OpLang
tcOpLang w@(HasType {})= pure w
tcOpLang (Opaque s) = throwError ("Untyped opaque: " <> show s)
tcOpLang (Union a b) = do
   a' <- tcLang a
   b' <- tcLang b
   unify (lTy a') (lTy b')
   pure $ HasType Inferred (OpLang $ Union a' b') (lTy a')
tcOpLang (Unpack l vs body) = do
  l' <- tcLang l
  case lTy l' of
    TupleTyp tys -> do
      body' <- local (M.union (M.fromList (zipStrict vs tys))) (tcLang body)
      pure $ HasType Inferred (OpLang $ Unpack l' vs body') (lTy body')
    _ -> throwError ("tcOpLang: Unpack on non-record: " <> prettyS l')
tcOpLang (Let v e body) = do
   e' <- tcExpr e
   body' <- local (M.insert v (nTy e')) (tcLang body)
   pure $ HasType Inferred (OpLang $ Let v e' body') (lTy body')
tcOpLang (Call e) = do
    e' <- tcExpr e
    pure $ HasType Inferred (OpLang $ Call e') (nTy e')
tcOpLang w@(Force (Thunk sym _args)) = do
    symTy  <- lookupVar (unSource sym)
    pure $ HasType Inferred (OpLang w) (ListTy symTy)
tcOpLang (Group op body) = do
  body' <- tcLang body
  keyTy <- mapTyKey (lTy body')
  outTy <- checkOp op =<< mapTyVal (lTy body')
  pure $ HasType Inferred (OpLang $ Group op body') (ListTy $ TupleTyp [keyTy, outTy])
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

unify :: HasCallStack => ExprType -> ExprType -> M ()
-- unify a b | trace ("unify: " <> prettyS (a,b)) False = undefined
unify (UnificationVar v) (UnificationVar v')
  | v > v' = unify (UnificationVar v') (UnificationVar v)
  | v == v' = pure ()
unify (UnificationVar v) r = do 
  uLookup v >>= \case
    Nothing -> uInsert v r
    Just l -> unify l r
unify l (UnificationVar v) = unify (UnificationVar v) l
unify (ListTy l) (ListTy r) = unify l r
unify (TupleTyp l) (TupleTyp r) = zipStrict l r & traverse_ (uncurry unify)
unify l r = unless (l == r) $ throwError ("unify: " <> show l <> " /= " <> show r <> prettyCallStack callStack)


uLookup :: Int -> M (Maybe ExprType)
uLookup uvar = do
  uvars <- gets uEnv
  pure $ M.lookup uvar uvars
uInsert :: Int -> ExprType -> M ()
uInsert uvar ty = do
  uvars <- gets uEnv
  modify $ \s -> s { uEnv = M.insert uvar ty uvars }
freshUVar :: M ExprType
freshUVar = do
  uvar <- gets uNext
  modify $ \s -> s { uNext = uvar + 1 }
  pure (UnificationVar uvar)




assert :: (MonadError s m) => Bool -> s -> m ()
assert True _ = pure ()
assert False msg = throwError msg

-- tcExpr (Nest es) = do

lookupVar :: HasCallStack => Var -> M ExprType
lookupVar v = asks (M.lookup v) >>= \case
  Just ty -> pure ty
  Nothing -> throwError $ "Variable not in scope: " ++ show v
