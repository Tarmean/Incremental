{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DataKinds #-}
module Rewrites where

import CompileQuery
import Control.Monad.Trans
import Control.Monad.Trans.Elevator
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Data
import qualified Data.Set as S
import qualified Data.Map.Lazy as LM
import qualified Data.Map.Strict as M
import OpenRec
import Data.Functor.Identity
import Data.Semigroup (Max(..))
import Data.Monoid (First(..))
import Data.Foldable (asum)
import Data.Coerce (Coercible, coerce)
import Control.Monad.Reader (MonadReader, ReaderT)

-- recompExprType :: TypeEnv -> ScopeEnv -> Expr -> ExprType
-- recompExprType env scope (Ref v) = fromMaybe AnyType (scope LM.!? tyData v <|> tableTys env LM.!? tyData v)
-- recompExprType _env _scope (Proj _ i v) = case etyOf v of
--   TupleTyp ls -> ls !! i
--   _ -> error "Projection of non-tuple"
-- recompExprType _env _scope (BOp _ op _ _) = case op of
--     Eql -> EBase $ typeRep (Proxy :: Proxy Bool)
-- recompExprType _ _ _ = AnyType

-- recompLangType :: Lang' a -> ExprType
-- recompLangType = \case
--   Comprehend _ _ _ _ _ e -> etyOf e
--   Return e -> etyOf e
--   _ -> AnyType

-- recompTypes :: TopLevel -> TopLevel
-- recompTypes e0 =  outLevel
--   where
--      outLevel = runReader (runT t e0) LM.empty
--      out = TE (LM.fromList [ (unSource k, ltyOf v) | (k,(_args, v)) <- LM.toList (defs e0) ]) mempty
--      t =
--          trans (\rec -> \case
--            (w@Comprehend {cBound}::Lang) -> recompLang <$> local (M.union $ boundEnv cBound) (rec w)
--            w -> recompLang <$> rec w)
--         |||
--          trans (\rec a ->
--            recompExpr =<< rec a)
--         |||
--          recurse
--      boundEnv :: [(Var, Typed Var)] -> M.Map Var ExprType
--      boundEnv = M.fromList . map (second tyType)
--      recompLang e = setLangType e $ recompLangType e
--      recompExpr e = do
--         scope <- ask
--         pure $ setExprType e (recompExprType out scope e)

-- setLangType :: Lang' a -> ExprType -> Lang' a
-- setLangType l t = case l of
--   Comprehend {} -> l { eTyp = t }
--   Return e -> Return e

-- setExprType :: Expr -> ExprType -> Expr
-- setExprType expr t = case expr of
--   Ref v -> Ref v { tyType = t }
--   Proj _ i e -> Proj t i e
--   BOp _ op a b -> BOp t op a b


tagWithFrees :: TopLevel -> TopLevel
tagWithFrees tl = tl { defs = defs' }
  where
    defs' = M.map (\(_args, e) -> (escaped e, e)) (defs tl)
    escaped e = filter (\x -> Source x `M.notMember` defs tl) (S.toList $ freeVarsQ e)

nullTypes :: Data a => a -> a
nullTypes = runIdentity .: runT $
   trans_ (\(_ :: ExprType) -> pure (error "Nulled Type")) ||| recurse


newtype VarGenT m a = VarGenT { runVarGenT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadTrans)
  deriving (MonadState s) via Elevator (StateT Int) m
  deriving (MonadReader s) via Elevator (StateT Int) m
class Monad m => MonadVar m where
    genVar :: String -> m Var
instance Monad m => MonadVar (VarGenT m) where
    genVar s = VarGenT $ do
        i <- get
        put (i + 1)
        pure (Var i s)
deriving via Elevator (StateT s) m instance MonadVar m => MonadVar (StateT s m) 
deriving via Elevator (WriterT s) m instance (Monoid s, MonadVar m) => MonadVar (WriterT s m) 
deriving via Elevator (ReaderT s) m instance (MonadVar m) => MonadVar (ReaderT s m) 
instance (MonadTrans t, Monad (t m), MonadVar m) => MonadVar (Elevator t m) where
    genVar = lift . genVar
withVarGenT :: Monad m => Int -> VarGenT m a -> m a
withVarGenT i = flip evalStateT i . runVarGenT

withVarGenT' :: Int -> VarGenT m a -> m (a, Int)
withVarGenT' i = flip runStateT i . runVarGenT

-- calcArity :: 


type LiftFuns m = StateT (M.Map Fun ([Local], Lang)) (VarGenT m)
maxVar :: Data a => a -> Int
maxVar = getMax . runQ (
     query (\rec -> \case
       LRef @'Flat v -> Max (uniq v)
       a -> rec a)
 ||| query (\rec -> \case
       Ref @'Flat v -> Max (uniq v)
       a -> rec a)
 ||| recurse)



bindGuardT :: Lang -> Maybe Lang
-- bindGuardT a
--   | trace ("bindGuardT " ++ show a) False = undefined
bindGuardT (Bind (Filter g (Return Unit)) _ e ) = Just (Filter g e)
bindGuardT _ = Nothing

bindBindT :: Lang' t -> Maybe (Lang' t)
bindBindT (Bind (Bind e1 v e2) v' e3) = Just (Bind e1 v (Bind e2 v' e3))
bindBindT _ = Nothing

bindUnitT :: Lang' t -> Maybe (Lang' t)
bindUnitT (Bind (Return Unit) _ e) = Just e
bindUnitT _ = Nothing

bindRightUnitT :: Lang' t -> Maybe (Lang' t)
bindRightUnitT (Bind m v (Return (Ref v'))) | v == v' = Just m
bindRightUnitT _ = Nothing

bindLeftUnitT :: Lang -> Maybe Lang
bindLeftUnitT (Bind (Return a) v e) = Just (subst v a e)
bindLeftUnitT _ = Nothing

trivialThunk :: Expr -> Maybe Expr
trivialThunk (AThunk (Thunk (Source s) [])) = Just (Ref s)
trivialThunk _ = Nothing

trivPack :: Expr -> Maybe Expr
trivPack (Pack [x]) = Just (Ref x)
trivPack _ = Nothing

simpPass :: Data a => a -> a
simpPass = runIdentity . runT (
   recurse >>> completelyTrans' (langRewrites ||| exprRewrites))
  where
   langRewrites = tryTrans $ useFirst [bindGuardT, bindBindT, bindUnitT, bindRightUnitT, bindLeftUnitT]
   exprRewrites = tryTrans trivPack
   useFirst = ala First mconcat


ala :: forall s m n a0. (Coercible (m s) (n s)) => (m a0 -> n a0) -> ([n s] -> n s) -> [s -> m s] -> s -> m s
ala _cons folder args = coerce out
  where
     args'  = coerce args :: [s -> n s]
     out x = folder (args' <&> x)
     (<&>) fs a= ($ a) <$> fs
    

subst :: Var -> Expr -> Lang -> Lang
subst v sub = runIdentity . runT (
    tryTrans (\case
       (Ref v'::Expr) | v == v' -> Just sub
       _ -> Nothing)
    -- |||
    -- tryTrans (\case
    --    (LRef v'::Lang) | v == v' -> Just sub
    --    _ -> Nothing)
    ||| recurse)

nestedToThunks :: TopLevel -> TopLevel
nestedToThunks tl0 = runIdentity $ runT (trans_ nestToThunk &&& trans_ dropDumbThunk &&& recurse) tl
  where
    tl = tagWithFrees tl0
    nestToThunk :: Expr -> Identity Expr
    nestToThunk (Nest (LRef r)) = pure $ AThunk (Thunk (Source r) (argsOf r))
    nestToThunk (AggrNested op (LRef r)) = pure $ Aggr op (Thunk (Source r) (argsOf r))
    nestToThunk a = pure a
    dropDumbThunk :: Expr -> Identity Expr
    dropDumbThunk (AThunk (Thunk (Source a) [])) = pure $ Ref a
    dropDumbThunk a = pure a
    argsOf :: Var -> [Var]
    argsOf v = case LM.lookup (Source v) (defs tl) of
      Just ([], _) -> error (show v <> " Did you forgot to run optPass before nestedToThunks?")
      Just (args, _) -> args
      Nothing 
        | otherwise -> error ("Undefined function" <> show v)
dropTopLevel :: TopLevel' p -> TopLevel' p
dropTopLevel a = a { defs = M.map dropDefs (defs a) }
  where
    dropDefs (l,r) = (filter ((`M.notMember` defs a) . Source) l, r)

    -- aggrToFun :: Monad m => Expr -> LiftFuns m Expr
    -- aggrToFun (Aggr op r)
    --     | frees <- S.toList (freeVarsQ r)
    --     , not (null frees) = do
    --        v <- Fun <$> genVar "F"
    --        modify (M.insert v (frees, l))
    --        pure (ThunkArg v AnyType (fmap Ref frees))

    -- hoistFuncs (Thunk f es) = do
    --     (vs, l) <- gets (M.! f)
    --     pure (Call f (zipWith (\v e -> BOp Eql (ValArg e) (ValArg (Ref v))) vs es))

-- inlineReturns :: 
