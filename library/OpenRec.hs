{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | Helpers for AST traversals
module OpenRec where

import Data.Data hiding (gmapM)
import Control.Monad.Writer.Strict (Writer, MonadWriter (tell), execWriter, WriterT, execWriterT)
import Control.Monad ((<=<))
import Debug.Trace (trace)
import Control.Monad.Trans (lift)
import qualified Data.HashSet as S
import HitTest (Answer(..), hitTest, Oracle(..), typeRepOf)
import Data.Functor.Identity (runIdentity, Identity)


-- | Data gives us a way to get the type of a value, and to traverse its children
type Trans1 m = forall x. Data x => x -> m x
-- | VTable for our traversal
data Ctx m = Ctx {
  -- | Continuation when case matched
  onSuccess :: Trans1 m,
  -- | Continuation when case failed
  onFailure :: Trans1 m,
  -- | Top-level vtable for recursion
  onRecurse :: Trans1 m
  }
-- | A traversal collects a relevant sets of types to visit,
-- and a visitor functions to apply to those types
data Trans m = T {
    -- | Types for which @withCtx@ may succeed
    relevant :: !(S.HashSet TypeRep),
    -- | Should we recurse when the current type is not in @relevant@, but contains @relevant@ types?
    -- True, iff @withCtx@ would call @recurse@.
    toplevelRecursion :: Bool,
    -- | Actualy transformation  function
    withCtx :: Ctx m -> Trans1 m
}

runT' :: Data a => Trans Identity -> a -> a
runT' trans a0 = runIdentity (f a0)
  where
    Oracle oracle = hitTest a0 (relevant trans)
    f :: forall x. Data x => x -> Identity x
    f x = case oracle x of
      Hit _ -> withCtx trans (Ctx pure pure f) x
      Follow -> if toplevelRecursion trans then gmapM f x else pure x
      Miss -> pure x

-- | The core run function
runT :: forall m a. (Monad m, Data a) => Trans m -> a -> m a
runT trans a0 = f a0
  where
    Oracle oracle = hitTest a0 (relevant trans)
    f :: forall x. Data x => x -> m x
    f x = case oracle x of
      Hit _ -> withCtx trans (Ctx pure pure f) x
      Follow -> if toplevelRecursion trans then gmapM f x else pure x
      Miss -> pure x

-- [Note: Oracle]
-- Types form a tree. We have a root type @a@, which is the type of the value we are transforming.
--
-- - Each type @t@ has a set of sub-types @reachable(t)@, which are accessible from its Data.Data instance.
-- - Each transformation has a set of relevant types
--
-- So our logic is:
-- - If a type @t@ is relevant, apply the transformation (duh)
-- - If we could reach a relevant type from @t@, recurse into @t@
-- - Otherwise, do nothing
--
-- There is a subtlety: If the transformation won't recurse, we shouldn't either!
-- So we also track if the transformation would recurse, and only recurse if it would.

-- | @runT@ specialized for the Writer monad
runQ :: forall a o. (Monoid o, Data a) => Trans (Writer o) -> a -> o
runQ t m = execWriter (runT t m)

-- | @runT@ specialized for the WriterT transformer
runQT :: forall a o m. (Monad m, Monoid o, Data a) => Trans (WriterT o m) -> a -> m o
runQT t m = execWriterT (runT t m)

-- | @gmapM@ from Data.Data, but only using an Applicative constraint
gmapM :: forall m a. (Data a, Applicative m) => (forall d. Data d => d -> m d) -> a -> m a
gmapM f = gfoldl k pure
  where
    k :: Data d => m (d -> b) -> d -> m b
    k c x = c <*> f x

-- | Alternative composition of transformations
-- In @a ||| b@, we only run @b@ if @a@ fails.
(|||) :: forall m. Monad m => Trans m -> Trans m -> Trans m
l ||| r = T relevantTypes containsRecursion trans
  where
    relevantTypes = relevant l `S.union` relevant r
    containsRecursion = toplevelRecursion l || toplevelRecursion r
    trans :: Ctx m -> Trans1 m
    trans ctx = withCtx l (ctx { onFailure = withCtx r ctx })
infixl 1 |||

-- | Sequential composition of transformations
-- In @a >>> b@, we only run @b@ if @a@ succeeds.
(>>>) :: forall m. Monad m => Trans m -> Trans m -> Trans m
l >>> r = T relevantTypes containsRecursion trans
  where
    relevantTypes = relevant l `S.union` relevant r
    containsRecursion = toplevelRecursion l
    trans :: Ctx m -> Trans1 m
    trans ctx = withCtx l ctx{ onSuccess = withCtx r ctx }
infixl 1 >>>


-- | Definite composition of transformations
-- In @a >>> b@, we always run @a@ then @b@.
(&&&) :: forall m. Monad m => Trans m -> Trans m -> Trans m
l &&& r = T relevantTypes containsRecursion trans
  where
    relevantTypes = relevant l `S.union` relevant r
    containsRecursion = toplevelRecursion l || toplevelRecursion r
    trans :: Ctx m -> Trans1 m
    trans ctx = withCtx l ctx{ onSuccess = withCtx r ctx, onFailure = withCtx r ctx }
infixl 1 &&&

-- | Core recursion operator
-- Usually, we either want top down recursion
--
-- @
-- tryTrans_ @Expr \case
--    Minus x y | x == y -> Just (Const 0)
--    _ -> Nothing
-- ||| recurse
-- @
--
-- Or bottom up recursion:
--
-- @
-- recurse >>>
-- tryTrans_ @Expr \case
--    Minus x y | x == y -> Just (Const 0)
--    _ -> Nothing
-- @
recurse :: Monad m => Trans m
recurse = T mempty True $ \Ctx{..} -> onSuccess <=< gmapM onRecurse

tryQueryM :: forall a o m. (Monad m, Monoid o, Data a) => ((forall x. Data x => x -> m o) -> a -> Maybe (m o)) -> Trans (WriterT o m)
tryQueryM f = T (onlyRel @a) False $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f (execWriterT . onRecurse) a' of
      Nothing -> onFailure a'
      Just o -> lift o >>= tell >> onSuccess a'
  Nothing -> onFailure a'

{-# INLINE onlyRel #-}
onlyRel :: forall a. Typeable a => S.HashSet TypeRep
onlyRel = S.singleton (typeRepOf @a)
tryQuery :: forall a o. (Monoid o, Data a) => ((forall x. Data x => x -> o) -> a -> Maybe o) -> Trans (Writer o)
tryQuery f = T (onlyRel @a) False $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f (execWriter . onRecurse) a' of
      Nothing -> onFailure a'
      Just o -> tell o >> onSuccess a'
  Nothing -> onFailure a'
tryQuery_ :: forall a o m. (Monad m, Monoid o, Data a) => (a -> Maybe o) -> Trans (WriterT o m)
tryQuery_ f = T (onlyRel @a) False $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f a' of
      Nothing -> onFailure a'
      Just o -> tell o *> onSuccess a'
  Nothing -> onFailure a'

tryTrans :: forall a m. (Monad m, Data a) => (a -> Maybe a) -> Trans m
tryTrans f = T (onlyRel @a) False $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> case f a of
     Nothing -> onFailure a
     Just a' -> onSuccess a'
  Nothing -> onFailure a

tryTransM :: forall a m. (Monad m, Data a) => (Trans1 m -> a -> Maybe (m a)) -> Trans m
tryTransM f = T (onlyRel @a) False $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> case f onRecurse a of
     Nothing -> onFailure a
     Just ma' -> onSuccess =<< ma'
  Nothing -> onFailure a
tryTransM_ :: forall a m. (Monad m, Data a) => (a -> Maybe (m a)) -> Trans m
tryTransM_ f = tryTransM (\_ -> f)
tryTrans_ :: forall a m. (Monad m, Data a) => (a -> Maybe a) -> Trans m
tryTrans_ f = tryTransM (\_ -> fmap pure . f)

completelyTrans' :: forall m. (Monad m) => Trans m -> Trans m
completelyTrans' f = T (relevant f) (toplevelRecursion f) $ \Ctx{..} a0 -> 
  let 
    fixCtx suc = Ctx { onSuccess = trace "sucFix" . fixpoint True, onFailure = if suc then onSuccess else onFailure, onRecurse = onRecurse }
    fixpoint :: Data a => Bool -> a -> m a
    fixpoint suc = withCtx f (fixCtx suc)
  in fixpoint False a0

completelyTrans :: forall a m. (Monad m, Data a) => (a -> Maybe a) -> Trans m
completelyTrans f = tryTrans (fixpoint False)
  where
    fixpoint suc a = case f a of
      Nothing -> if suc then Just a else Nothing
      Just a' -> fixpoint True a'

-- stop recursion here, nested `recurse` statements will jump to the block
block :: forall m. Trans m -> Trans m
block (T rel tlRec f) = T rel tlRec $ \Ctx{..} ->
    let rec :: Data x => x -> m x
        rec = f (Ctx onSuccess onFailure rec)
    in rec

(.:) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(.:) = (.).(.)
