{-# LANGUAGE LambdaCase #-}
-- | Use congruence closure+rewrite rules to reason about SQL queries
module CongruenceClosure where


import qualified Data.Map.Strict as M
import Control.Monad.State

import Data.Equality.Matching.Database
import Data.Equality.Matching

import qualified CompileQuery as Q
import qualified SQL


-- [Note: Why E-Graphs]
--
-- Take this query:
--
-- @
-- SELECT U.user_id, J.sum
-- FROM users U
--   INNER JOIN
--     (SELECT J.user_id, SUM(J.cost) as sum FROM jobs J GROUP BY J.user_id) J
--    ON U.user_id = J.user_id
-- @
--
-- Is it equivalent to the following?
-- @
-- SELECT J.user_id, SUM(J.cost) as sum
-- FROM jobs J
-- WHERE J.user_id in (SELECT U.user_id FROM users)
-- GROUP BY J.user_id J
-- @
--
-- Yes, but only if the users table has user_id as primary key. If so, then for
-- each tuple in `jobs` there is only one `user`, so we can shift the join
-- inside the GROUP BY without affecting cardinalities. From there, we can use
-- equality reasoning to replace `U.user_id` with `J.user_id`, at which point
-- we have no reference to `U` and can turn it into an existential join. If
-- there is a foreign key constraint, we can even get rid of the WHERE clause.
--
--
-- But this reasoning is complicated and fraught with peril. The fundep chasing is
-- a hypergraph breadth-first search. The equality reasoning is hash-consing.
-- The foreign key reasoning can be expressed as propagating `not_null(p)` in
-- datalog-like rules. They all have to be interleaved.
--
-- E-Graphs support all of this, so we go with them.

-- [Note: Formalism]
--
-- One approach in the literature focuses on semigroups. Queries are a logic formula which check whether an argument tuple is in the result. 
--
--  So `FROM users U` becomes `exists U. U \in users & ...`. This `U` stands for a specific tuple in the database, not just its values. You can think of it as a memory address, though e.g. join results do not map to static tables.
--
--  We can make existential quantifiers implicit and always pull them to the top-level.
--
--
--  Aggregates do not quite fit this thought process.
--


data SomeValue a
    = Name Q.Var
    | Proj Q.Var SQL.AField
    | SkolemFun SkolemIdent [a]
    | Joined a a
    | JoinProj1 a
    | JoinProj2 a
    | Try a

type SkolemIdent = String

-- data PatEnv lang = PatEnv { uniqSupply :: Int, matchLang :: M.Map (lang Var) Var }
-- type M lang =  State (PatEnv lang)

-- toQuery :: (Traversable l, Ord (l Var)) => Pattern l -> M l Var
-- toQuery (VariablePattern v) = pure v
-- toQuery (NonVariablePattern l) = traverse toQuery l >>= resolveMatch

-- compileToQuery :: (Traversable l, Ord (l Var)) => Pattern l -> (Var, M.Map (l ClassIdOrVar) ClassIdOrVar)
-- compileToQuery p = (pOut, outMap)
--   where
--     (pOut, envOut) = runState (toQuery p) (PatEnv (maxVar p+1) mempty)
--     outMap = M.mapKeysMonotonic (fmap CVar) $ M.map CVar $ matchLang envOut

-- -- | Generate a fresh variable
-- nextVar :: M l Var
-- nextVar = do
--    i <- gets uniqSupply
--    modify $ \s -> s { uniqSupply = uniqSupply s + 1}
--    pure i

-- -- | HashCons for variable patterns
-- resolveMatch :: (Ord (l Var)) => l Var -> M l Var
-- resolveMatch matcher =
--     gets (M.lookup matcher . matchLang) >>= \case
--         Just existingName -> pure existingName
--         Nothing -> do
--            newName <- nextVar
--            modify $ \s -> s { matchLang = M.insert matcher newName (matchLang s) }
--            pure newName


-- maxVar :: Foldable l => Pattern l -> Var
-- maxVar l = maximum (0:vars l)
--   where
--     vars (VariablePattern v) = [v]
--     vars (NonVariablePattern l') = concatMap vars l'

