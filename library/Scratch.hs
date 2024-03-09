{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE GADTs #-}
module Scratch where
import Control.Lens

data Foo where
  Foo :: (a -> (String,Int)) -> Foo


fooL :: Functor f => (forall x. (x -> (String,Int)) -> f (x -> (String,Int))) -> Foo -> f Foo
fooL k (Foo p) = Foo <$> k p




-- overN :: Functor f => (forall x. a -> f a)


