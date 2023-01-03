{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use const" #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module OpenRec where

import Data.Data hiding (gmapM)
import Control.Monad.Writer.Strict (Writer, MonadWriter (tell), execWriter, WriterT, execWriterT)
import Control.Monad ((<=<))
import Control.Applicative ((<|>))
import Debug.Trace (trace)
import Control.Monad.Trans (lift)
import qualified Data.HashSet as S
import HitTest (Answer(..), hitTest, Oracle(..), typeRepOf)


type Trans1 m = forall x. Data x => x -> m x
data Ctx m = Ctx {
  onSuccess :: Trans1 m,
  onFailure :: Trans1 m,
  onRecurse :: Trans1 m
  }
data Trans m = T { relevant :: !(S.HashSet TypeRep), withCtx :: Ctx m -> Trans1 m}


runT :: forall m a. (Monad m, Data a) => Trans m -> a -> m a
runT (T hs a) a0 = f a0
  where
    Oracle oracle = hitTest a0 hs
    f :: forall x. Data x => x -> m x
    f x = case oracle x of
      Hit _ -> a (Ctx pure pure f) x
      Follow -> gmapM f x
      Miss -> pure x

runQ t m = execWriter (runT t m)
runQ :: forall a o. (Monoid o, Data a) => Trans (Writer o) -> a -> o

runQT :: forall a o m. (Monad m, Monoid o, Data a) => Trans (WriterT o m) -> a -> m o
runQT t m = execWriterT (runT t m)

gmapM :: forall m a. (Data a, Applicative m) => (forall d. Data d => d -> m d) -> a -> m a
gmapM f = gfoldl k pure
  where
    k :: Data d => m (d -> b) -> d -> m b
    k c x = c <*> f x

infixl 1 |||
(|||) :: Trans m -> Trans m -> Trans m
T rel1 l ||| T rel2 r = T (S.union rel1 rel2) $ \c@Ctx {onSuccess, onRecurse} -> l (Ctx onSuccess (r c) onRecurse)

(.|||) :: (a -> Maybe a) -> (a -> Maybe a) -> a -> Maybe a
f .||| g = \x -> f x <|> g x

tryType :: forall a b. (Typeable a, Typeable b) => (a -> Maybe a) -> (b -> Maybe b)
tryType a x = case eqT @a @b of
  Just Refl -> a x
  _ -> Nothing

infixl 1 &&&
(&&&) :: Monad m => Trans m -> Trans m -> Trans m
T rel1 l &&& T rel2 r = T (S.union rel1 rel2) $ \c@Ctx {onRecurse} -> l (Ctx (r c) (r c) onRecurse)

infixl 2 >>>
(>>>) :: Monad m => Trans m -> Trans m -> Trans m
T rel1 l >>> T rel2 r = T (S.union rel1 rel2) $ \c@Ctx{..} -> l (Ctx (r c) onFailure onRecurse)

recurse :: Monad m => Trans m
recurse = T mempty $ \Ctx{..} -> onSuccess <=< gmapM onRecurse

tryQueryM :: forall a o m. (Monad m, Monoid o, Data a) => ((forall x. Data x => x -> m o) -> a -> Maybe (m o)) -> Trans (WriterT o m)
tryQueryM f = T (onlyRel @a) $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f (execWriterT . onRecurse) a' of
      Nothing -> onFailure a'
      Just o -> lift o >>= tell >> onSuccess a'
  Nothing -> onFailure a'

{-# INLINE onlyRel #-}
onlyRel :: forall a. Typeable a => S.HashSet TypeRep
onlyRel = S.singleton (typeRepOf @a)
tryQuery :: forall a o. (Monoid o, Data a) => ((forall x. Data x => x -> o) -> a -> Maybe o) -> Trans (Writer o)
tryQuery f = T (onlyRel @a) $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f (execWriter . onRecurse) a' of
      Nothing -> onFailure a'
      Just o -> tell o >> onSuccess a'
  Nothing -> onFailure a'
tryQuery_ :: forall a o m. (Monad m, Monoid o, Data a) => (a -> Maybe o) -> Trans (WriterT o m)
tryQuery_ f = T (onlyRel @a) $ \Ctx {..} (a' :: a') -> case eqT @a @a' of
  Just Refl -> case f a' of
      Nothing -> onFailure a'
      Just o -> tell o *> onSuccess a'
  Nothing -> onFailure a'

tryTrans :: forall a m. (Monad m, Data a) => (a -> Maybe a) -> Trans m
tryTrans f = T (onlyRel @a) $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> case f a of
     Nothing -> onFailure a
     Just a' -> onSuccess a'
  Nothing -> onFailure a

tryTransM :: forall a m. (Monad m, Data a) => (Trans1 m -> a -> Maybe (m a)) -> Trans m
tryTransM f = T (onlyRel @a) $ \Ctx{..} (a::a') -> case eqT @a @a' of
  Just Refl -> case f onRecurse a of
     Nothing -> onFailure a
     Just ma' -> onSuccess =<< ma'
  Nothing -> onFailure a
tryTransM_ :: forall a m. (Monad m, Data a) => (a -> Maybe (m a)) -> Trans m
tryTransM_ f = tryTransM (\_ -> f)
tryTrans_ :: forall a m. (Monad m, Data a) => (a -> Maybe a) -> Trans m
tryTrans_ f = tryTransM (\_ -> fmap pure . f)

completelyTrans' :: forall m. (Monad m) => Trans m -> Trans m
completelyTrans' f = T (relevant f) $ \Ctx{..} a0 -> 
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
block (T rel f) = T rel $ \Ctx{..} ->
    let rec :: Data x => x -> m x
        rec = f (Ctx onSuccess onFailure rec)
    in rec

(.:) :: (b -> c) -> (a1 -> a2 -> b) -> a1 -> a2 -> c
(.:) = (.).(.)
