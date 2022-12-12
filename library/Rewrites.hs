{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Rewrites where

import CompileQuery
import Control.Monad.Trans
import Control.Monad.Trans.Elevator
import Control.Monad.State
import Control.Monad.Writer.Strict
import Data.Data
import qualified Data.Set as S
import qualified Data.Map.Lazy as LM
import qualified Data.Map.Strict as M
import OpenRec
import Control.Monad.Reader (local, MonadReader (..), runReader)
import Data.Bifunctor (Bifunctor(..))
import Data.Functor.Identity
import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))
import Data.Semigroup (Max(..))

recompExprType :: TypeEnv -> ScopeEnv -> Expr -> ExprType
recompExprType env scope (Ref v) = fromMaybe AnyType (scope LM.!? tyData v <|> tableTys env LM.!? tyData v)
recompExprType _env _scope (Proj _ i v) = case etyOf v of
  TupleTyp ls -> ls !! i
  _ -> error "Projection of non-tuple"
recompExprType _env _scope (BOp _ op _ _) = case op of
    Eql -> EBase $ typeRep (Proxy :: Proxy Bool)
recompExprType _ _ _ = AnyType

recompLangType :: Lang' a -> ExprType
recompLangType = \case
  Comprehend _ _ _ _ _ e -> etyOf e
  Return e -> etyOf e
  _ -> AnyType

recompTypes :: TopLevel -> TopLevel
recompTypes e0 =  outLevel
  where
     outLevel = runReader (runT t e0) LM.empty
     out = TE (LM.fromList [ (unSource k, ltyOf v) | (k,(_args, v)) <- LM.toList (defs e0) ]) mempty
     t =
         trans (\rec -> \case
           (w@Comprehend {cBound}::Lang) -> recompLang <$> local (M.union $ boundEnv cBound) (rec w)
           w -> recompLang <$> rec w)
        |||
         trans (\rec a ->
           recompExpr =<< rec a)
        |||
         recurse
     boundEnv :: [(Var, Typed Var)] -> M.Map Var ExprType
     boundEnv = M.fromList . map (second tyType)
     recompLang e = setLangType e $ recompLangType e
     recompExpr e = do
        scope <- ask
        pure $ setExprType e (recompExprType out scope e)

instance FreeVars Lang where
   freeVars = freeVarsQ
setLangType :: Lang' a -> ExprType -> Lang' a
setLangType l t = case l of
  Comprehend {} -> l { eTyp = t }
  Return e -> Return e

setExprType :: Expr -> ExprType -> Expr
setExprType expr t = case expr of
  Ref v -> Ref v { tyType = t }
  Proj _ i e -> Proj t i e
  BOp _ op a b -> BOp t op a b


freeVarsQ :: Data a => a -> S.Set (Typed Var)
freeVarsQ = runQ $
     query (\rec -> \case
       Ref @Var v -> S.singleton v
       a -> rec a)
 ||| query (\rec -> \case
       (w@Comprehend {cBound} :: Lang) -> rec w S.\\ boundVars cBound
       a -> rec (a::Lang))
 ||| recurse
 where
   boundVars :: [(Var, Typed Var)] -> S.Set Local
   boundVars binder = S.fromList [ Typed var (tyType body) | (var,body) <- binder ]

nullTypes :: Data a => a -> a
nullTypes = runIdentity .: runT $
   trans_ (\(_ :: ExprType) -> pure (error "Nulled Type")) ||| recurse
(.:) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(.:) = (.).(.)


newtype VarGenT m a = VarGenT { runVarGenT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadTrans)
  deriving (MonadState s) via Elevator (StateT Int) m
class Monad m => MonadVar m where
    genVar :: String -> m Var
instance Monad m => MonadVar (VarGenT m) where
    genVar s = VarGenT $ do
        i <- get
        put (i + 1)
        pure (Var i s)
deriving via Elevator (StateT s) m instance MonadVar m => MonadVar (StateT s m) 
deriving via Elevator (WriterT s) m instance (Monoid s, MonadVar m) => MonadVar (WriterT s m) 
instance (MonadTrans t, Monad (t m), MonadVar m) => MonadVar (Elevator t m) where
    genVar = lift . genVar

-- calcArity :: 

overBody :: Functor m => (Expr -> m Expr) -> Out -> m Out
overBody f a = Out (target a) <$> f (expr a)

type LiftFuns m = StateT (M.Map Fun ([Local], Lang)) (VarGenT m)
maxVar :: Data a => a -> Int
maxVar = getMax . runQ (
     query (\rec -> \case
       Ref @Var v -> Max (uniq (tyData v))
       a -> rec a)
 ||| recurse)

withVarGenT :: Monad m => Int -> VarGenT m a -> m a
withVarGenT i = flip evalStateT i . runVarGenT

nestedToThunks :: TopLevel -> TopLevel
nestedToThunks tl = runIdentity $ runT (trans_ collectionArgToFun ||| recurse) tl
  where
    argsOf :: Var -> [Local]
    argsOf v = case LM.lookup (Source v) (defs tl) of
      Just (args, _) -> args
      Nothing -> error "Undefined function"
    collectionArgToFun :: SomeArg -> Identity SomeArg
    collectionArgToFun (CollArg l) = pure (ThunkArg (Source l) AnyType (fmap Ref (argsOf l)))
    collectionArgToFun other = pure other

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
