{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
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
import Prettyprinter (Pretty, pretty)
import UnpackStructs (flattenType)

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
    defs' = M.fromList $ either error fst $ runExcept (runReaderT (runStateT (defs_ >>= setUVars) emptyUnificationEnv) topLevel)
    defs_ = do
        let topVars = M.keys (defs tl)
        freshVars (map unSource topVars) $ \bound -> do
            ls <- traverse (overSecond elabLang) $ M.toList $ defs tl
            topTys <- traverse (setUVars . lTy . snd . snd) ls
            -- traceM $ show (zipWith addListTy (map fst ls) topTys)
            let unifyResultsTys = zip bound topTys
            traverse_ (uncurry unify) unifyResultsTys
            let unifyListSourceTys = zip bound (zipWith addListTy ls topTys)
            traverse_ (uncurry unify) unifyListSourceTys
            pure ls
    topLevel = mempty

addListTy :: (Source, ([Var], Lang)) -> ExprType -> ExprType
addListTy (_, ([],_)) (ListTy _ t) = ListTy RootTy t
addListTy (s, (_:_,_)) (ListTy _ t) = ListTy (SourceTy s) t
addListTy _ _ = error "not a list ty"

fillUVars :: ExprType -> M ExprType
fillUVars (TupleTyp t) = TupleTyp <$> traverse fillUVars t
fillUVars (ListTy k t) = ListTy <$> fillUVars k <*> fillUVars t
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
data ErrCtx = CtxLang Lang | CtxExpr Expr | NoCtx
instance Pretty ErrCtx where
  pretty (CtxLang lang) = pretty lang
  pretty (CtxExpr lang) = pretty lang
  pretty NoCtx = pretty "?"
data UnificationEnv = UnificationEnv { uEnv :: M.Map UVar ExprType, uNext :: UVar, lastContext :: ErrCtx }
emptyUnificationEnv :: UnificationEnv
emptyUnificationEnv = UnificationEnv M.empty 0 NoCtx
type M = StateT UnificationEnv (ReaderT Env (Except Error))

withExpr :: Expr -> M a -> M a
withExpr e m = do
   oldCtx <- gets lastContext
   modify $ \s -> s { lastContext = CtxExpr e }
   out <- m
   modify $ \s -> s { lastContext = oldCtx }
   pure out
withLang :: Lang -> M a -> M a
withLang e m = do
   oldCtx <- gets lastContext
   modify $ \s -> s { lastContext = CtxLang e }
   out <- m
   modify $ \s -> s { lastContext = oldCtx }
   pure out


nTy :: HasCallStack => Expr -> ExprType
nTy (HasEType _ _ ty) = ty
nTy a = error ("nTy: not a HasEType\n" <> prettyS a)

lTy :: HasCallStack => Lang -> ExprType
lTy (OpLang (HasType _ _ ty)) = ty
lTy l = error ("lTy: not a HasEType\n" <> prettyS l)

-- Rewrite it into a normal form with an HasEType on top
tcThunk :: Thunk -> M ExprType
tcThunk (Thunk sym _) = do
   lookupVar (unSource sym)
   -- pure thunkOut

tcExpr :: Expr -> M Expr
tcExpr w = withExpr w (tcExprW w)
tcExprW :: Expr -> M Expr
tcExprW e@(HasEType {}) = pure e
tcExprW (Ref r) = setEType (Ref r) <$> lookupVar r
tcExprW w@(Lit lit) = case lit of
   IntLit _ -> pure (setEType w intTy)
   StrLit _ -> pure (setEType w stringTy)
tcExprW (AThunk thunk) = do
   thunkTy <- tcThunk thunk
   pure $ setEType (AThunk thunk) thunkTy
tcExprW (Proj i tot e) = do
   e' <- tcExpr e
   case nTy e' of
      TupleTyp tys -> pure $ setEType (Proj i tot e') (tys !! i)
      uv@UnificationVar {} -> do
         v <- replicateM tot freshUVar
         _ <- unify uv (TupleTyp v)
         pure $ setEType (Proj i tot e) (v !! i)
      _ -> throwError ("tcExpr: Proj on non-record" <> show e)
tcExprW Unit = pure $ setEType Unit (TupleTyp [])
tcExprW (Tuple es) = do
   es' <- traverse tcExpr es
   pure $ setEType (Tuple es') (TupleTyp (map nTy es'))
tcExprW (BOp op a b) = do
  a' <- tcExpr a
  b' <- tcExpr b
  outTy <- checkEOp op (nTy a') (nTy b') 
  pure $ setEType (BOp op a' b') outTy
tcExprW (Aggr op thunk) = do
  thunkTy <- tcThunk thunk
  outTy <- checkOp op thunkTy
  pure $ setEType (Aggr op thunk) outTy
tcExprW (AggrNested op t) = do
  sourceTy <- tcLang t
  oTy <- checkOp op (lTy sourceTy)
  pure $ setEType (AggrNested op t) oTy
tcExprW (Nest n) = do
  sourceTy <- tcLang n
  uv <- freshUVar
  pure $ setEType (Nest n) (ListTy uv (lTy sourceTy))
tcExprW l@(Lookup source _) = do
   sourceTy <- lookupVar (unSource source)
   keyTy <- freshUVar
   valTy <- freshUVar
   origin <- freshUVar
   _ <- unify sourceTy (ListTy origin (TupleTyp [keyTy, valTy]))
   pure $ hasEType l valTy
tcExprW (Slice l r total tuple) = do
   tuple <- tcExpr tuple
   case nTy tuple of
      TupleTyp ls -> pure $ hasEType (Slice l r total tuple) (TupleTyp (slice l r (flattenType ls)))
      _ -> error "Illegal Slice"

slice :: Int -> Int -> [a] -> [a]
slice left right ls = take (right - left) (drop left ls)

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
tcLang w = withLang w (tcLangW w)
tcLangW :: Lang -> M Lang
tcLangW (Bind generator v body) = do
   generator' <- tcLang generator
   ty <- case lTy generator' of
     ListTy _ ty -> pure ty
     ov@UnificationVar {} -> do
       v' <- freshUVar
       uv <- freshUVar
       _ <- unify ov (ListTy uv v')
       pure v'
     o -> throwError $ "tcLang: Bind on non-list: " <> prettyS o <> "\n" <> prettyS generator'
   body' <- local (M.insert v ty) (tcLang body)
   setType (Bind generator' v body') (lTy body')
tcLangW (Return expr) = do
   expr' <- tcExpr expr
   uv <- freshUVar
   setType (Return expr') (ListTy uv $ nTy expr')
tcLangW (Filter expr body) = do
   expr' <- tcExpr expr
   assert (nTy expr' == EBase (typeRep @Bool)) "tcLang: Filter on non-bool"
   body' <- tcLang body
   setType (Filter expr' body') (lTy body')
tcLangW (LRef r) = do
   ty <- lookupVar r
   setType (LRef r) ty
tcLangW (OpLang l) = OpLang <$> tcOpLang l
tcLangW (AsyncBind {}) = error "tcLang: Not Unnested before typechecking"

tcOpLang :: OpLang -> M OpLang
tcOpLang w@(HasType {})= pure w
tcOpLang (Opaque s) = throwError ("Untyped opaque: " <> show s)
tcOpLang (Union a b) = do
   a' <- tcLang a
   b' <- tcLang b
   oTy <- unify (lTy a') (lTy b')
   pure $ HasType Inferred (OpLang $ Union a' b') oTy
tcOpLang (Unpack l vs body) = do
  l' <- tcExpr l
  case nTy l' of
    TupleTyp tys -> do
      body' <- local (M.union (M.fromList [ (a,b) | (Just a, b) <- zipStrict vs tys])) (tcLang body)
      pure $ HasType Inferred (OpLang $ Unpack l' vs body') (lTy body')
    _ -> throwError ("tcOpLang: Unpack on non-record: " <> prettyS l')
tcOpLang (Distinct e) = do
    e' <- tcLang e
    pure $ HasType Inferred (OpLang $ Distinct e') (lTy e')
tcOpLang (Let v e body) = do
   e' <- tcExpr e
   body' <- local (M.insert v (nTy e')) (tcLang body)
   pure $ HasType Inferred (OpLang $ Let v e' body') (lTy body')
tcOpLang (Call e) = do
    e' <- tcExpr e
    ty' <- cleanSource (nTy e')
    pure $ HasType Inferred (OpLang $ Call e') ty'
tcOpLang w@(Force (Thunk sym _args)) = do
    symTy  <- lookupVar (unSource sym)
    ty' <- cleanSource symTy
    pure $ HasType Inferred (OpLang w) ty'
tcOpLang (Group ops body) = do
  body <- tcLang body
  kty <- freshUVar
  vty <- freshUVar
  sourceTy <- freshUVar
  _ <- unify (lTy body) (ListTy sourceTy (TupleTyp [kty, vty]))
  outTys <- forM ops $ \op -> checkOp op (ListTy sourceTy vty)
  uv <- freshUVar
  pure $ HasType Inferred (OpLang $ Group ops body) (ListTy uv $ TupleTyp [kty, TupleTyp outTys])
  -- where
  --   mapTyKey :: ExprType -> M ExprType
  --   mapTyKey (ListTy _ (TupleTyp (a:_))) = pure a
  --   mapTyKey ty = error ("mapTyVal: not a key-value pair: " <> show ty)
  --   mapTyVal :: ExprType -> M ExprType
  --   mapTyVal (ListTy k (TupleTyp (_:b))) = pure $ ListTy k (TupleTyp b)
  --   mapTyVal ty = error ("mapTyVal: not a key-value pair: " <> show ty)


cleanSource :: ExprType -> M ExprType
cleanSource (ListTy _ a) = do
  pure $ ListTy LocalTy a
cleanSource (UnificationVar v) = do
      tty <- freshUVar
      ety <- freshUVar
      oty <- unify (UnificationVar v) (ListTy tty ety)
      case oty of
        ListTy _ a -> do
          pure $ ListTy LocalTy a
        _ -> error "cleanSource: impossible"
cleanSource o = error ("cleanSource: not a list: " <> show o)

checkEOp :: BOp -> ExprType -> ExprType -> M ExprType
checkEOp op lty rty = do
  case op of
    Eql -> do
      _ <- unify lty rty
      pure boolTy
    And -> do
      _ <- unify lty boolTy
      _ <- unify rty boolTy
      pure boolTy
    Mult -> do
      _ <- unify lty intTy
      _ <- unify rty intTy
      pure intTy
checkOp :: AggrOp -> ExprType -> M ExprType
checkOp op ty = do
  st <- freshUVar
  _ <- unify (ListTy st (inpTy op)) ty 
  pure (outTy op)
  where
    inpTy _ = EBase (typeRep @Int)
    outTy _ = EBase (typeRep @Int)

zipStrict :: [a] -> [b] -> [(a, b)]
zipStrict [] [] = []
zipStrict (a:as) (b:bs) = (a, b) : zipStrict as bs
zipStrict _ _ = error "zipStrict: lists of different length"

unify :: HasCallStack => ExprType -> ExprType -> M ExprType
unify = go
 where
    go (UnificationVar v) (UnificationVar v')
      | v > v' = go (UnificationVar v') (UnificationVar v)
      | v == v' = pure (UnificationVar v)
    go (UnificationVar v) r = do 
      uLookup v >>= \case
        Nothing -> r <$ uInsert v r
        Just l -> go l r
    go l (UnificationVar v) = go (UnificationVar v) l
    go (ListTy k l) (ListTy k' r) = ListTy <$> go k k' <*> go l r
    go (TupleTyp l) (TupleTyp r) 
      | length l == length r = TupleTyp <$> (zipStrict l r & traverse (uncurry go))
    go l r 
      | l == r = pure l
      | otherwise = pure r
      | otherwise = do
        ctx <- gets lastContext
        throwError ("unify: " <> show l <> " /= " <> show r <> prettyCallStack callStack <> "\nctx: " <> prettyS (l,r, ctx))


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
