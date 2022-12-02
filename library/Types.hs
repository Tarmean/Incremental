{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NoAllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Types where
import Data.Kind (Type)
import Data.Dynamic (Dynamic)


infixr 0 :~>
data a :~> b = FOp {
   deltas :: Delta a -> Delta b,
   base :: a -> b
}

class (Delta (Delta a) ~ Delta a, Monoid (Delta a)) => Deltas a where
    type family Delta (a :: Type) :: Type
instance (Deltas a, Deltas b) => Deltas (a :~> b) where
    type Delta (a :~> b:: Type) = Delta a :~> Delta b
instance (Semigroup (Delta b), Semigroup b) => Semigroup (a :~> b) where
    FOp d1 b1 <> FOp d2 b2 = FOp (d1 <> d2) (b1 <> b2)
instance (Monoid (Delta b), Monoid b) => Monoid (a :~> b) where
    mempty = FOp mempty mempty
mkOp :: (Deltas a, Delta a ~ a, Delta b ~ b) => (a -> b) -> a :~> b
mkOp f = FOp {deltas = f, base = f}

data Expr a where
   BOp :: (Deltas a, Deltas l, Deltas r) => {
      impl :: l :~> r :~> a,
      lhs :: Expr l,
      rhs :: Expr r
   } -> Expr a
   UOp :: {
      uopBase :: Expr a,
      mapped :: a :~> b
   } -> Expr b
   ForEach :: {
       body :: Expr [a],
       cont :: Expr a -> Expr [b]
   } -> Expr [b]
   Const :: Deltas a => {
       value :: a
   } -> Expr a
   Fold :: {
       coll :: Expr [a],
       step :: b -> a -> b,
       zero :: b
   } -> Expr b
   -- Integrate :: Deltas b => {
   --     collI :: Expr [Delta b],
   --     stepI :: b -> Delta b -> b,
   --     zeroI :: b
   -- } -> Expr b
   -- -- Prior :: {
   -- --     expr :: Expr a
   -- -- } -> Expr a
   -- Differentiate :: (a ~ Delta b) => {
   --     unfoldBase :: Expr b
   -- } -> Expr [a]
   Var :: Dynamic -> Expr a


interpDelta :: Expr a -> Delta a
interpDelta (BOp op l r)
    = op `deltas` interpDelta l `deltas` interpDelta r
    <> op `base` interpExpr l `deltas` interpDelta r
    -- <> op `deltas` interpDelta l `base` interpDelta r
interpDelta (UOp a op) = op `deltas` interpDelta a
interpDelta (Const _) = mempty
interpDelta (Var _) = undefined

interpExpr :: Expr a -> a
interpExpr = undefined
-- interpExpr (BOp op l r) = base (base op (interpExpr l)) (interpExpr r)
-- interpExpr (Const a) = a
-- interpExpr (UOp f a) = base a (interpExpr f)
-- interpExpr (ForEach coll cont) = concatMap (interpExpr . cont . Const) (interpExpr coll)
-- -- interpExpr (Fold coll step zero) = foldl step zero (interpExpr coll)
-- -- interpExpr (Integrate coll step zero) = foldl step zero (scanl (<>) mempty (interpExpr coll))
-- -- interpExpr (Differentiate _) = undefined
-- interpExpr (Var _) = undefined
