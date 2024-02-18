{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE LambdaCase #-}
module DemandAnalysisTransform where
import CompileQuery
import DemandAnalysis
import Control.Monad.State
import Control.Monad.Cont
import Rewrites (MonadVar (genVar), withVarGenT, maxVar)
import Data.Functor.Identity
import qualified Data.Map.Strict as M
import OpenRec
import Control.Monad


data VarTree = VarTree Var [VarTree] | BindAs Var | UnUsed deriving (Eq, Ord, Show)

varTreeToExpr :: VarTree -> Expr
varTreeToExpr (VarTree _ ls) = tuple (map varTreeToExpr ls)
varTreeToExpr (BindAs v) = Ref v
varTreeToExpr UnUsed = Unit

varTreeToUnpack :: Var -> VarTree -> Lang -> Lang
varTreeToUnpack v varTree bod = runIdentity $ runContT (bindVarTree (Ref v) varTree) (const $ pure bod)
bindVarTree :: Monad m => Expr -> VarTree -> ContT Lang m ()
bindVarTree v (VarTree _ ls) = do
   bound <- forM ls $ \l -> do
      case l of
          BindAs v' -> pure (Just v')
          UnUsed -> pure Nothing
          VarTree b ls' -> do
             bindVarTree (Ref b) (VarTree b ls')
             pure (Just b)
   wrapInner (OpLang .  Unpack v bound)
bindVarTree _ UnUsed = pure ()
bindVarTree v (BindAs v') 
  | v == Ref v' = pure ()
  | otherwise = wrapInner (OpLang . Let v' v)


newArgs :: VarTree -> [Var]
newArgs = newArgs'
  where
    newArgs' (VarTree _ ls) = concatMap newArgs ls
    newArgs' (BindAs v) = [v]
    newArgs' UnUsed = []

wrapInner :: Functor m => (Lang -> Lang) -> ContT Lang m ()
wrapInner f = ContT $ \ar -> f <$> ar ()

demandToProj :: MonadVar m => Var -> Demand -> m VarTree
demandToProj v NoInfo = pure (BindAs v)
demandToProj v (Each _) = pure $ BindAs v
demandToProj _ NoneUsed = pure UnUsed
demandToProj v (Tup ls) = VarTree v <$> traverse go ls
  where
    go NoneUsed = pure UnUsed
    go NoInfo = BindAs <$> genVar "b"
    go (Each _) = BindAs <$> genVar "bs"
    go (Tup ls') = do
        v' <- genVar "b"
        VarTree v' <$> traverse go ls'


transpileThunk :: MonadVar m => M.Map Source [Demand] -> Thunk -> ContT Lang m Thunk
transpileThunk m t@(Thunk v args) = case m M.!? v of
   Nothing -> pure t
   Just dmds -> do
      os <- forM (zip dmds args) $ \(dmd, arg) -> do
         varTree <- demandToProj arg dmd
         bindVarTree (Ref arg) varTree
         pure (newArgs varTree)
      pure (Thunk v (concat os))

transpileAsyncBind :: MonadVar m => M.Map Source [Demand] -> [(Var, Maybe AggrOp, Thunk)] -> Lang -> m Lang
transpileAsyncBind m binds bod = flip runContT (const $ pure bod) $ do
    thunks' <- forM binds $ \(v, op, thunk) -> do
        thunk' <- transpileThunk m thunk
        pure (v, op, thunk')
    wrapInner (AsyncBind thunks')

transformAllBinds :: MonadVar m => M.Map Source [Demand] -> Trans m
transformAllBinds m = tryTransM_ (\case
    AsyncBind binds bod -> Just (transpileAsyncBind m binds bod)
    _ -> Nothing) ||| recurse

transformFunDef :: MonadVar m => M.Map Source [Demand] -> Source -> ([Var], Lang) -> m ([Var], Lang) 
transformFunDef m source (args, body) = do
    case m M.!? source of
      Nothing -> pure (args, body)
      Just dmds -> do
          ls <- forM (zip dmds args) $ \(dmd, arg) -> do
              varTree <- demandToProj arg dmd
              pure (newArgs varTree, OpLang . Let arg (varTreeToExpr varTree))
          let (args', bods) = unzip ls
              body' = foldr ($) body bods
          pure (concat args', body')


applyDemandAnalysis :: MonadVar m => M.Map Source [Demand] -> TopLevel -> m TopLevel
applyDemandAnalysis m (TopLevel defs root) = do
    defs <- runT (transformAllBinds m) defs
    defs <- M.traverseWithKey (transformFunDef m) defs
    pure (TopLevel defs root)


dropDeadArgs :: TopLevel -> TopLevel
dropDeadArgs tl = runIdentity $ withVarGenT (maxVar tl) $ applyDemandAnalysis dmds tl
  where
    GlobalEnv dmds = fixDemands tl

data WorkerWrapper = WorkerWrapper { wwSource :: Source, wwArgs :: [(Var, VarTree)] }
