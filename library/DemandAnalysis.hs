-- {-# OPTIONS_GHC -dsuppress-coercions -ddump-prep -fforce-recomp -O2 #-}
module DemandAnalysis (bar) where
import Data.Data (Data)
import qualified Data.Map.Strict as M
import CompileQuery (Var)
import qualified Data.Set as S
import Control.Monad.State (StateT)
import Rewrites (VarGenT, MonadVar (genVar))
import Control.Monad.State.Strict

{-# NOINLINE foo #-}
foo :: (Int,Int) -> Int
foo a = fst a + fst a
-- Node 0 [Node 1 [],Node 3 []] :-> [0,1] :+ TupleD [Top]
--
-- 0:@[1:@[], 2:@[]] :-> [0,1] :+ TupleD [Top]

data PatTree = Node Id [PatTree]
  deriving (Eq, Ord, Show, Data)
type Id = String


{-# NOINLINE bar #-}
bar :: (Int,Int) -> (Int,Int)
bar (a,b) = (a*2,a+b)
--
-- bar :: a@(b,c) :-> a+(b, b+c)

data Core
  = Lambda String Core
  | Core :@ Core
  | Ref Id
  | Tup [Core]
  | Proj Int Int Core
  | Const String
  deriving (Eq, Ord, Show, Data)
fooC :: Core
fooC = Lambda "a" (Const "+" :@ (Const "fst" :@ Ref "a") :@ (Const "fst" :@ Ref "a"))

type M = VarGenT (State (M.Map Id Demand))
toDemandF :: Core -> M Demand
toDemandF (Ref f) = pure $ [f] :+ Top
toDemandF (Tup ls) =(\x ->  [] :+ TupleD x) <$> traverse toDemandF ls
toDemandF (Proj i n l) = do
  ls <- replicateM n (DRef <$> genVar "x")
  v :+ ld <- toDemandF l
  unifyD (TupleD (fmap ([] :+) ls)) ld
  pure  (v :+ (ls !! i))
  -- toDemandF l
  -- v :+ TupleD ls -> v +:+ (ls !! i)
  -- v :+ d -> v :+ ProjD i d
toDemandF (Ref d :@ a) =  undefined

unifyD :: DemandF -> DemandF -> M ()
unifyD = undefined

-- (+:+) :: [Id] -> Demand -> Demand
-- (+:+) ls (v :+ d) = (ls ++ v) :+ d

-- | Demands for absence analysis
data DemandF
  = PatTree :-> Demand -- ^ Function call demand
  | TupleD [Demand] -- ^ Tuple whose fields have demands
  | DApp Var [DemandF]
  | DRef Var
  | Top
  | Bot
  deriving (Eq, Ord, Show, Data)
data Demand = [Id] :+ DemandF
  deriving (Eq, Ord, Show, Data)

-- -- | Merge sequential demands
-- join :: Demand -> Demand -> Demand
-- join Absent d = d
-- join d Absent = d
-- join Used _ = Used
-- join _ Used = Used
-- join (ListD d1) (ListD d2) = ListD (join d1 d2)
-- join (TupleD ds1) (TupleD ds2) = TupleD (zipWith join ds1 ds2)
-- join _ _ = error "join: incompatible demands"

data DmdType = DmdType {
   dmdEnv :: M.Map Var Demand,
   dmdArgs :: [Demand]
 }

-- type Ana l = l -> Demand -> (DemandEnv, )
-- absenceAna :: Expr 

