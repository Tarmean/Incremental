{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExplicitNamespaces #-}
module OpenRec where

import Data.Data hiding (gmapM)
import Control.Monad.Writer.Strict (Writer, MonadWriter (tell), execWriter)
-- import Control.Monad.Writer.Strict (WriterT, runWriterT, tell)

-- fixme, add
type Trans1 m = forall x. Data x => x -> m x
data Ctx m = Ctx {
  onSuccess :: Trans1 m,
  onFailure :: Trans1 m,
  onRecurse :: Trans1 m
  }
newtype Trans m = T { withCtx :: Ctx m -> Trans1 m}


runT :: forall m a. (Monad m, Data a) => Trans m -> a -> m a
runT (T a) = f
  where
    f :: Data x => x -> m x
    f = a (Ctx pure pure (gmapM f))

runQ :: forall a o. (Monoid o, Data a) => Trans (Writer o) -> a -> o
runQ (T a) x = execWriter (f x)
  where
    f :: Data x => x -> (Writer o) x
    f = a (Ctx pure pure (gmapM f))

gmapM :: forall m a. (Data a, Applicative m) => (forall d. Data d => d -> m d) -> a -> m a
gmapM f = gfoldl k pure
  where
    k :: Data d => m (d -> b) -> d -> m b
    k c x = c <*> f x

infixl 1 |||
(|||) :: Trans m -> Trans m -> Trans m
T l ||| T r = T $ \c@Ctx {onSuccess, onRecurse} -> l (Ctx onSuccess (r c) onRecurse)

infixl 1 &&&
(&&&) :: Monad m => Trans m -> Trans m -> Trans m
T l &&& T r = T $ \c@Ctx {onRecurse} -> l (Ctx (r c) (r c) onRecurse)

infixl 2 >>>
(>>>) :: Monad m => Trans m -> Trans m -> Trans m
T l >>> T r = T $ \c@Ctx{..} -> l (Ctx (r c) onFailure onRecurse)

recurse :: Trans m
recurse = T $ \Ctx{..} -> onRecurse

query :: forall a o. (Monoid o, Data a) => ((forall x. Data x => x -> o) -> a -> o) -> Trans (Writer o)
query f = T $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> a' <$ tell (f (execWriter . onRecurse) a')
  Nothing -> onFailure a'

trans :: forall a m. (Monad m, Data a) => (Trans1 m -> a -> m a) -> Trans m
trans f = T $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> onSuccess =<< f onRecurse a
  Nothing -> onFailure a

trans_ :: forall a m. (Monad m, Data a) => (a -> m a) -> Trans m
trans_ f = T $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> onSuccess =<< f a
  Nothing -> onFailure a

-- stop recursion here, nested `recurse` statements will jump to the block
block :: forall m. Trans m -> Trans m
block (T f) = T $ \Ctx{..} ->
    let rec :: Data x => x -> m x
        rec = f (Ctx onSuccess onFailure rec)
    in rec

withRec :: forall m. (Trans1 m -> Trans m) -> Trans m
withRec f = T $ \c@Ctx{..} -> f onRecurse `withCtx` c

-- loop :: forall m. Monad m => Maybe Int -> Trans m -> Trans m
-- loop limit (T m) = T $ \c -> 
--   let
--     go :: Data x => Int -> x -> m x
--     go b x
--       | Just l <- limit
--       , b >= l = tell (Any $ b > 0) >> pure x
--     go b x = case m c x of
--       TM (Const (Any True) :*: o) -> o >>= go (b+1)
--       TM (_ :*: o) -> TM (Const (Any (b > 0)) :*: o)
--   in go 0
