{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BlockArguments, LambdaCase #-}
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
--   (SELECT P.user_id, SUM(P.cost) FROM purchases P GROUP BY P.user_id) PQ
--    ON U.user_id = PQ.user_id
-- @
--
-- Can we move the @users@ join into the group? Yes, iff:
--
-- - there is only one user per user_id (fundep)
-- - the database allows us to select fields unique by fundep (not oracle)
--
-- But doing the transformation is tough. We must figure out which values determine which other values.
--
-- - from join condition: (U.user_id -> P.user_id, P.user_id -> U.user_id)
-- - (U.user_id -> U, U -> U.*)
-- - (PQ -> PQ.*, P -> P.*)
-- - from groupby (P.user_id -> PQ, PQ -> P.user_id)
--
-- We can chase these implications like so:
--
-- - P -> P.user_id -> PQ
-- - PQ -> P.user_id -> P
--
-- Therefore the join is linear and we can flatten them into a single select
--
-- This could be phrased as a single-table datalog program.
-- We use a variable watchlist scheme akin to sat solvers to do this chasing efficiently.
--
-- TODO: Cache transitive @a -> ...@ implications with a single source to speed up common cases?
-- Cache invalidation would be so painful, though
-- Ironically exactly what differential dataflow would be good at
module FundepAnalysis where

import WatchlistPropagator
import OpenRec
import Control.Monad.Writer (execWriterT, tell)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import CompileQuery (TableMeta(..), FunDeps(..), Var (Var))
import Control.Monad.State.Strict
import SQL
import Control.Monad.Reader
import Prettyprinter


infixr 5 :.
data NId = Root | NId :. String | ARef Var
  deriving (Eq, Ord, Show)
instance Pretty NId where
    pretty = \case
        Root -> "Root"
        a :. b -> pretty a <> "." <> pretty b
        ARef a -> pretty a
pattern (:-) :: Ord n => n -> [n] -> AClause n
pattern (:-) a b  <- (makeFrom -> (a,b))
  where
    (:-) nId nids = AClause nId (S.fromList nids)
makeFrom :: AClause n -> (n, [n])
makeFrom (AClause a b) = (a, S.toList b)


newtype Env = Env {
   constraints :: [AClause NId]
 }


-- [Note: isLocalSource]
--
-- When we have an equality filter
--
-- > WHERE X.a = Y.a
--
-- we usually want to unify @X.a@ and @Y.a@.
-- But if the equality is in a lateral query from the sources it may not, e.g.:
--
-- @
-- SELECT *
-- FROM
--    a A, b B
--    LATERAL LEFT OUTER JOIN (SELECT 1 WHERE a.x = b.x) C
-- @
--
-- That type of query is weird, but we still have to check for it.
-- It should be safe if at least one of the variables is locally bound
--
-- TODO: Add more logic once outer joins are better supported
type M = ReaderT (M.Map Var NId) (State Env)
withLocals :: (MonadReader (M.Map k a1) m, Ord k) => [(k, a1)] -> m a2 -> m a2
withLocals l = local (M.union (M.fromList l))

toGraph :: SQL -> FEnv NId
toGraph sql = fromClauses clauses
  where Env clauses = execState (runReaderT (makeGraph Root sql) mempty) (Env mempty) 

userTable, jobTable :: SQL
userTable = Table (TableMeta (FD [["user_id"]]) ["user_id", "name"]) "users"
jobTable = Table (TableMeta (FD [["job_id"]]) ["user_id", "job_id", "cost"]) "jobs"

aTest :: SQL
aTest = ASPJ (SPJ {
  sources = [(Var 2 "U", userTable), (Var 3 "PQ", aggrTable)],
  wheres = [Eql (Ref (Var 2 "U") "user_id") (Ref (Var 3 "PQ") "user_id")],
  proj = M.fromList [("user_id", Ref (Var 2"U") "user_id"), ("name", Ref (Var 2 "U") "name"), ("agg", Ref (Var 3 "PQ") "agg")]
        })
  -- sources = [(Var 2 "U", userTable), (Var 3 "PQ", aggrTable), (Var 4 "PQ2", aggrTable2)],
  -- wheres = [Eql (Ref (Var 2 "U") "user_id") (Ref (Var 3 "PQ") "user_id"),Eql (Ref (Var 2 "U") "user_id") (Ref (Var 4 "PQ2") "user_id")],
  -- proj = M.fromList [("user_id", Ref (Var 2"U") "user_id"), ("name", Ref (Var 2 "U") "name"), ("agg", Ref (Var 3 "PQ") "agg"), ("agg2", Ref (Var 4 "PQ2") "agg")]
    where
     aggrTable =
      GroupQ [Ref (Var 1 "J") "user_id"] $
      ASPJ SPJ {
        sources = [(Var 1 "J", jobTable)],
        wheres = [],
        proj = M.fromList [("user_id", Ref (Var 1 "J") "user_id"), ("agg", AggrOp SumO (Ref (Var 1 "J") "cost"))]
      }
     -- aggrTable2 =
     --  GroupQ [Ref (Var 1 "J") "user_id"] $
     --  ASPJ SPJ {
     --    sources = [(Var 1 "J", jobTable)],
     --    wheres = [],
     --    proj = M.fromList [("user_id", Ref (Var 1 "J") "user_id"), ("agg", AggrOp MaxO (Ref (Var 1 "J") "cost"))]
     --  }

mkRef :: NId -> Var -> NId
mkRef _self = ARef
makeGraph :: NId -> SQL -> M ()
makeGraph self (OrderBy _ spj) = makeGraph self spj
makeGraph self (ASPJ spj) = do
    let isLocalSource k = any ((==k) . fst) spj.sources
    withLocals [(v, mkRef self v) | (v,_) <- spj.sources ] $ do
        self <-> [self :. k | k <- M.keys spj.proj]
        forM_ (M.toList spj.proj) $ \(k,v) -> do
            mkExpr (self :. k) v
        forM_ spj.sources $ \(k,v) -> do
            makeGraph (mkRef self k) v
        forM_ spj.wheres $ \v -> do
            case v of
              -- See Note isLocalSource
              Eql (Ref l x) (Ref r y)
                | isLocalSource l || isLocalSource r -> do
                  l <- resolveLocal l
                  r <- resolveLocal r
                  (l :. x) <-> [r :. y]
              _ -> pure ()
makeGraph self (Slice _ _ e) = makeGraph self e
makeGraph self (Table (TableMeta (FD fds) fields) _) = do
    self <-> [self :. field | field <- fields]
    forM_ fds $ \fd -> self .- [self :. f | f <- fd ]
makeGraph self (GroupQ groups source) = do
   -- just use the same node for the group-by and the nested select
   -- the scoping is a bit weird, though
   groupDeps <- traverse depsFor groups
   case sequence groupDeps of
       Nothing -> pure ()
       Just o -> self <-> concat o
   makeGraph self source

depsFor :: forall m. MonadReader (M.Map Var NId) m => Expr -> m (Maybe [NId])
depsFor e = execWriterT $ runT (
      tryTransM_ \case
        e@(Ref k v) -> Just do
           -- o <- resolveLocal k
           -- tell $ Just [o :. v]
           tell $ Just [ARef k :. v]
           pure e
        _ -> Nothing
  ||| recurse
        ) e

mkExpr :: NId -> Expr -> M ()
mkExpr nid (Ref v a) = do
   rv <- resolveLocal v
   nid <-> [rv :. a]
mkExpr _ _ = pure ()

resolveLocal :: MonadReader (M.Map Var NId) m => Var -> m NId
resolveLocal s = asks (M.findWithDefault (ARef s) s)

(<->) :: NId -> [NId] -> M ()
(<->) l rs = do
   l .- rs
   forM_ rs $ \r -> r .- [l]
(.-) :: NId -> [NId] -> M ()
(.-) k v = do
  modify $ \s -> s { constraints = (k :- v) :constraints s }
