{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ConstraintKinds #-}
module TypeTest where
import Data.Kind (Type, Constraint)


-- data AIs f = Is String | IsConst Int | IsF (f (AIs f))
class Fundep a b => Is a b (x::Type) | x a -> b where
--    makeIs :: a -> AIs f
instance Is a a a where
--   makeIs = Is
-- instance Is Int b where
--   makeIs = IsConst

-- bar :: 

class Fundep a b | a -> b
instance Fundep a b => Fundep a b
  
type Con :: (Type -> Type) -> Type -> Constraint
type Con f a = (forall x. Ord x => Ord (f x), Ord a)

foo :: Con f a => f (f a) -> f (f a) -> Bool
foo l r = l < r
-- type Con a = (forall (x::Type). Is a x)

-- foo = makeIs "foo"
