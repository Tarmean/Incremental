-- | Take rules @(a,b,c) -> d@ and derive all conclusions 
-- We do this using 1-literal-watchlist, similar to SAT solvers.
--
-- But we use an open-world-assumption, as with constructive logic
-- In a sat solver, we take a logic formula a OR b OR c. This creates 6 triggers, for `a is true`, `a is false`, ...
--
-- To encode the formula, we
--
-- - ssubscribe to 2 triggers, e.g. `a is false` and `b is false`
-- - if one of the triggers activates, perform a check:
--    - If there are >=2 non-active triggers remaining, ensure that we subscribe to 2
--    - If there is 1 remaining option, the corresponding variable must be true. Activate its trigger
--    - If no option is left, the formula is unsolvable
--
-- But in our case we never learn `x is false`. Sat solver work around this by creating extra rules, but for us it's simpler and faster to hard-code a unidirectional special-case
--
-- If we have the rules:
-- @(a -> b), (b,c) -> d@
--
-- And assert @a,c@, we would derive @a,b,c,d@.
{-# LANGUAGE DeriveGeneric, OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module WatchlistPropagator where

import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State.Strict
import Control.Lens
import Data.Generics.Labels ()
import GHC.Generics (Generic)

data AClause n = AClause !n !(S.Set n)
  deriving (Eq, Ord, Show)
data FEnv n = FEnv {
   active :: !(S.Set n),
   watchList :: !(M.Map n [AClause n]),
   pending :: !(S.Set n)
 } deriving (Eq, Ord, Show, Generic)

isActive :: Ord n => n -> FEnv n -> Bool
isActive v env = S.member v (active env)
process :: (Ord n, Foldable t) => t n -> FEnv n -> FEnv n
process v0 = execState (mapM_ publish v0 >> normalize)
normalize :: (Ord n, MonadState (FEnv n) m) => m ()
normalize = loop
  where
    loop = do
       p <- use #pending
       #pending .= mempty
       unless (S.null p) (mapM_ go (S.toList p) *> loop)
    go v = do
      use (#active . at v) >>= \case
        Just () -> pure ()
        Nothing -> do
          #active . at v .= Just ()
          clauses <- popWatchList v
          mapM_ makeWatch clauses

fromClauses :: Ord n => [AClause n] -> FEnv n
fromClauses c = execState (mapM_ makeWatch c) FEnv {active = mempty, watchList = mempty, pending=mempty}

makeWatch :: (Ord n, MonadState (FEnv n) m) => AClause n -> m ()
makeWatch c@(AClause vid clause) = do
  seen <- use #active
  unless (S.member vid seen) do
     case S.toList (clause S.\\ seen) of
        (x:_) -> #watchList . at x . non mempty %= (c:)
        _ -> publish vid

publish :: (Ord n, MonadState (FEnv n) m) => n -> m ()
publish cid = do
  seen <- use #active
  unless (S.member cid seen) do
    #active %= S.insert cid
    #pending %= S.insert cid
popWatchList :: (Ord n, MonadState (FEnv n) m) => n -> m [AClause n]
popWatchList v = do
  out <- use (#watchList . at v . non mempty)
  #watchList . at v .= Nothing
  pure out
