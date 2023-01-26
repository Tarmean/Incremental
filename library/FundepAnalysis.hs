{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- | Hunt down SQL fundeps
--
-- Problem:
--
-- @
-- SELECT *
-- FROM users U
--   INNER JOIN
--   (SELECT P.user_id, SUM(P.cost) FROM purchases P GROUP BY P.user_id) P
--    ON U.user_id = P.user_id
-- @
--
-- Can we move the @users@ join into the group? Yes, iff:
--
-- - there is only one user per user_id (fundep)
-- - the database allows us to select fields unique by fundep (not oracle)
--
-- But doing the transformation is tough. We must figure out which values determine which other values.
--
-- - @U.user_id = P.user_id@: They determine each other
-- - @FROM users U@: @U@ determines @.*@, @U.user_id@ determines @U@
-- - @GROUP BY P.user_id@: @P.user_id@ determines the grouped row
--
-- We turn these into implications @(a,b,c) -> d@, and perform boolean logic on the constraint graph.
-- We use a variable watchlist scheme akin to sat solvers.
--
-- TODO: Cache transitive @a -> ...@ implications to speed up common cases?
-- Cache invalidation would be so painful, though
-- Ironically exactly what differential dataflow would be good at
module FundepAnalysis where

import WatchlistPropagator
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Trans.Maybe
import Control.Monad.State.Strict
import SQL
import Control.Monad.Reader
import Control.Applicative


infixr 5 :.
data NId = Root | NId :. String | ARef String
  deriving (Eq, Ord, Show)
-- type (:-) :: V -> [V] -> AClause
pattern (:-) :: Ord n => n -> [n] -> AClause n
pattern (:-) a b  <- (makeFrom -> (a,b))
  where
    (:-) nId nids = AClause nId (S.fromList nids)
makeFrom :: AClause n -> (n, [n])
makeFrom (AClause a b) = (a, S.toList b)


newtype Env = Env {
   constraints :: [AClause NId]
 }


type M = ReaderT (M.Map Var NId) (State Env)
withLocals :: (MonadReader (M.Map k a1) m, Ord k) => [(k, a1)] -> m a2 -> m a2
withLocals l = local (M.union (M.fromList l))
makeGraph :: NId -> SQL -> M ()
makeGraph self (ASPJ spj) = do
    let isLocalSource k = any ((==k) . fst) spj.sources
    withLocals [(v, self :. v) | (v,_) <- spj.sources ] $ do
        self <-> [self :. k | k <- M.keys spj.proj]
        forM_ (M.toList spj.proj) $ \(k,v) -> do
            mkExpr (self :. k) v
        forM_ spj.sources $ \(k,v) -> do
            makeGraph (self :. k) v
        forM_ spj.wheres $ \v -> do
            case v of
              Eql (Ref l x) (Ref r y)
                | isLocalSource l || isLocalSource r -> do
                  -- if the equality is seperated from the sources it may not, e.g.:
                  --
                  -- SELECT *
                  -- FROM
                  --    a A, b B
                  --    LEFT OUTER JOIN (SELECT 1 WHERE a.x = b.x) C
                  l <- resolveLocal l
                  r <- resolveLocal r
                  (l :. x) <-> [r :. y]
              _ -> pure ()
makeGraph self (GroupQ groups source) = do
   -- just use the same node for the group-by and the nested select
   -- the scoping is a bit weird, though
   groupDeps <- traverse depsFor groups
   case sequence groupDeps of
       Nothing -> pure ()
       Just o -> self <-> concat o
   makeGraph self source

depsFor :: forall m. MonadReader (M.Map Var NId) m => Expr -> m (Maybe [NId])
depsFor = runMaybeT . go
  where
    go (Eql l r) = liftA2 (<>) (go l) (go r)
    go (Ref k v) = do
       o <- resolveLocal k
       pure [o :. v]

mkExpr :: NId -> Expr -> M ()
mkExpr nid (Ref v a) = do
   rv <- resolveLocal v
   nid <-> [rv :. a]
mkExpr _ _ = pure ()

resolveLocal :: MonadReader (M.Map Var NId) m => String -> m NId
resolveLocal s = asks (M.findWithDefault (ARef s) s)

(<->) :: NId -> [NId] -> M ()
(<->) l rs = do
   l .- rs
   forM_ rs $ \r -> r .- [l]
(.-) :: NId -> [NId] -> M ()
(.-) k v = do
  modify $ \s -> s { constraints = (k :- v) :constraints s }

         

-- data FundepGraph = FG {
    
    

-- }
