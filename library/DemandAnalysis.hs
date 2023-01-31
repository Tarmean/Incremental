-- {-# OPTIONS_GHC -dsuppress-coercions -ddump-simpl -fforce-recomp -O2 #-}
-- | Demand analysis
--
-- Given some code, we want to know how often free variables are used. This is a range such as:
--
-- Absent: used 0 times
-- Linear: 1 times
-- Strict: 1-n times
-- Maybe(Affine): 0-1 times
-- Lazy(Unknown): 0-n times
--
-- This part is pretty easy.
-- But! We want this knowledge not just for e.g. function arguments, but also for their fields. This way we can only pass the required fields, which is a huge deal.
--
-- We must do this analysis accross function boundaries which makes it difficult. The core trick is to match producers with consumers:
--
-- - Producing a struct may require different ressources for each field. Instead of merging this information into a flat set we can store a list of demands, one for each field.
-- - When we pattern-match, we can map the matched variables to the sub-demands.
--
-- GHC uses a cryptic short-notation for demands. 1P(L,ML) means:
-- - We have a struct of two fields which is always pattern-matched once
-- - The first fields is used 0-n times
-- - The second field is used 0-1 times, and its sub-fields are used 0-n times
--
module DemandAnalysis (bar) where
import Data.Data (Data)
import qualified Data.Map.Strict as M
import CompileQuery (Var(..))
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

 -- Str=<1P(LP(L),MP(L))>
{-# NOINLINE bar #-}
bar :: (Int,Int) -> (Int,Int)
bar (a,b) = (a*2,a+b)



--
-- bar : t
-- t ~ l -> r
-- l ~ (b,c)
-- b ~ I# c
-- d ~ I# e
-- r ~ &l + '(&b+c + 'I# _, &b+c+&d+e + 'I# _)
--
-- 1(L,L)
--
--
-- f . g
-- f : a -> b
-- g : b -> c
--
-- fst : (a,b) -> a
--
-- fst . bar : l@(b@(I# c),_) -> &l+&b+c + '(I# _)

--- first :: (a -> b) -> (a,c) -> (b,c)
--  first : f@(a -> b) -> l@(c,d) -> (l+f c, l+d)

data Core
  = Lambda Var Core
  | Core :@ Core
  | Ref Var
  | Tup [Core]
  | Proj Int Int Core
  | Const String
  deriving (Eq, Ord, Show, Data)

varA,varB :: Var
varA =  Var 0 "a"
varB =  Var 1 "b"
fooC :: Core
fooC = Lambda varA (Const "+" :@ (Const "fst" :@ Ref varA) :@ (Const "fst" :@ Ref varA))

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
toDemandF w@(:@) {} =  go w []
  where
    go (ls :@ a) acc = do
       a <- toDemandF a
       go ls (a : acc)
    go (Ref f) acc = pure $ [] :+ (DApp f acc)
    go a acc = do
       o <- toDemandF a
       v <- genVar "s"
       tellEq v o
       pure $ [] :+ DApp v acc
toDemandF (Const a) = undefined
toDemandF (Lambda v a) = (Node v [] :->) <$> toDemandF a

tellEq :: Var -> Demand -> VarGenT (State (M.Map Id Demand)) a0
tellEq = undefined

unifyD :: DemandF -> DemandF -> M ()
unifyD = undefined

-- (+:+) :: [Id] -> Demand -> Demand
-- (+:+) ls (v :+ d) = (ls ++ v) :+ d

-- | Demands for absence analysis
data DemandF
  = PatTree :-> Demand -- ^ Function call demand
  | TupleD [Demand] -- ^ Tuple whose fields have demands
  | DApp Var [Demand]
  | DRef Var
  | Top
  | Bot
  deriving (Eq, Ord, Show, Data)
data Demand = [Var] :+ DemandF
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

