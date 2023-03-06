{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module UnduplicateGrouping where


-- import OpenRec
-- import CompileQuery
-- import qualified Data.Map.Strict as M
-- import Data.Functor.Identity (Identity (runIdentity))
-- import Rewrites (VarGenT(..), genVar, MonadVar, withVarGenT, maxVar)
-- import Control.Monad.State.Strict
-- import Data.List (elemIndex)
-- import Data.Maybe (fromJust)



-- data Env = Env {
--     groupingBackwards :: M.Map Source (Source, AggrOp),
--     groupingForwards :: M.Map Source [AggrOp]
--  }


-- gatherEnv :: TopLevel -> Env
-- gatherEnv tl = Env backwards forwards
--   where
--     backwards = M.fromList [ (lhs, (Source rhs, op)) | (lhs, ([], OpLang g@Group {})) <- M.toList $ defs tl, let (rhs,op) = validGroup g ]
--     forwards = M.fromListWith (<>) [ (rhs, [op]) | (rhs, op) <- M.elems backwards ]

--     validGroup (Group _ _ [op] (LRef ref)) = (ref, op)
--     validGroup g = error ("Invalid group in gatherEnv. Did you run it immediately after the coroutine transform? " <> prettyS g)


-- type M = StateT (Env, M.Map Source Source) (VarGenT Identity)

-- generateGroupLabels :: MonadVar m => Env -> m (M.Map Source Source)
-- generateGroupLabels env = do
--     ls <- forM (M.toList $ groupingForwards env) $ \(source, _) -> do
--        newGrouper <- genVar "g"
--        pure (source, Source newGrouper)
--     pure $ M.fromList ls


-- resolveLookup :: Source -> M (Source, Int, Int)
-- resolveLookup source = do
--    (resolved, op) <- gets ((M.! source) . groupingBackwards . fst)
--    allOps <- gets ((M.! resolved) . groupingForwards . fst)
--    grouped <- gets ((M.! resolved) . snd)
--    pure (grouped, fromJust (elemIndex op allOps), length allOps)


-- mergeGroupingOps :: TopLevel -> TopLevel
-- mergeGroupingOps tl = runIdentity $ withVarGenT (maxVar tl) $ do
--     let env = gatherEnv tl
--     groupLabels <- generateGroupLabels env
--     tl <- evalStateT (runT renameLookupT tl) (env,groupLabels)
--     let
--       newGroups = M.fromList do
--           (k,ops) <- M.toList (groupingForwards env)
--           let newName = groupLabels M.! k
--           pure (newName, ([], OpLang $ Group 1 1 ops (LRef $ unSource k)))
--     pure tl { defs = M.union newGroups (defs tl M.\\ groupingBackwards env) }

-- renameLookupT :: Trans M
-- renameLookupT =
--   tryTransM_ @Expr \case
--     Lookup src args -> Just do
--        (res,idx, total) <- resolveLookup src
--        pure $ Proj idx total (Lookup res args)
--     _ -> Nothing
--  ||| recurse
