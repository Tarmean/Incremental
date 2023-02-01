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
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module DemandAnalysis (bar) where
import Data.Data (Data)
import qualified Data.Map.Strict as M
import CompileQuery (Var(..))
import qualified Data.Set as S
import Control.Monad.State (StateT)
import Rewrites (VarGenT, MonadVar (genVar), withVarGenT)
import Control.Monad.State.Strict
import Data.Functor.Identity (runIdentity)
import Control.Applicative
import Data.Either (partitionEithers)
import OpenRec (runT', tryTrans_, (|||), recurse)
import Data.Maybe (fromMaybe)

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

-- [\a -> e]p
-- [a]p~v1
-- v1 -> [e](p { a => without_hnf(v1), v1:hnf })
--
-- [c(a,b,c)]p
-- c([a]p, [b]p, [c]p)
-- 
-- [f a]p // by local copy
-- v1 ~ refresh_binders([f]p)
-- v2 ~ [a]p
-- v1 ~ v2 -> r
-- hnf(v1)+r
--
-- [f a]p // by global analysis
-- global(f) ~ l -> r
-- [a]p ~ l
-- r
--
-- [let x = e in b]p
-- v1 ~ [e]p
-- v2 ~ [b](p { x => without_hnf(v1), x:hnf(v1) })
--
-- [letrec x = e in b]p
-- v1 ~ [e](p { x => Ref l1, l1:v1 })
-- v2 ~ [b](p { x => Ref v1, l1:v1 })
--
-- [v]p if v is a variable
--p(v)
--
-- [case e of { c(v_1,...,v_n) -> e1 }]p
-- v1 ~ [e]p
-- v1 ~ (p_2,...,p_n)
-- v2 ~ [e1]{v_1 => p_2, ..., v_n => p_n}
-- hnf(e)+v2
--
-- [case e of { c(v_1,...,v_n) -> e1; c2(v_1,...v_m) -> e2;... }]p
-- v1 ~ [e]p
-- v1 ~ (c(p_1,...,p_n)|c2(p_1,...,p_m)|...)
-- v2 ~ [e1]{v_1 => p_2, ..., v_n => p_n}
-- v3 ~ [e2]{v_1 => p_2, ..., v_m => p_m}
-- v2 | v3

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

data Pat = Pat Constr [Var]
  deriving (Eq, Ord, Show, Data)
data Core
  = Lambda Var Core
  | Core :@ Core
  | Ref Var
  | Struct Constr [Core]
  | Case Core [(Pat,Core)]
  | Lit String
  deriving (Eq, Ord, Show, Data)

varA,varB :: Var
varA =  Var 0 "a"
varB =  Var 1 "b"
varC =  Var 2 "c"
fooC :: Core
fooC = Lambda varA (Case (Ref varA) [(Pat "Tuple2" [varB,varC], Struct "Tuple2" [Ref varC, Ref varB])])

sumV :: Var
sumV = Var 3 "sum"

sumC :: Core
sumC = Lambda varA (Case (Ref varA) [(Pat "ListCons" [varB,varC], Lit "+" :@ Ref varB :@ (Ref sumV :@ Ref varC)), (Pat "ListNil" [], Lit "0")])


runDemand :: Core -> Demand
runDemand c = runIdentity $ withVarGenT 0 (toDemandF c)

type M = VarGenT (State (M.Map Var Demand))
toDemandF :: MonadVar m => Core -> m Demand
toDemandF (Ref f) = pure $ DRef f
toDemandF (Struct constr ls) = Constructor constr <$> traverse toDemandF ls
toDemandF (Case expr cases) = do
  dexpr <- toDemandF expr
  dcases <- forM cases $ \(Pat constr args,bod) -> do
    vars <- traverse refreshVar args
    dbod <- toDemandF bod
    pure $ Unify dexpr (Constructor constr (map DRef vars)) &&& dbod
  pure (dexpr &&& ors dcases)
  
  -- pure 
  -- toDemandF l
  -- v :+ TupleD ls -> v +:+ (ls !! i)
  -- v :+ d -> v :+ ProjD i d
toDemandF (l :@ r) =  DApp <$> toDemandF l <*> toDemandF r
toDemandF (Lit _) = pure top
toDemandF (Lambda v a) = (v :->) <$> toDemandF a

refreshVar :: MonadVar m => Var -> m Var
refreshVar (Var _ b) = genVar b

(&&&) :: Demand -> Demand -> Demand
(&&&) a b = Ands [a,b]


ors :: [Demand] -> Demand
ors = Ors . concatMap flattenOrs
  where
    flattenOrs (Ors ls) = concatMap flattenOrs ls
    flattenOrs x = [x]

unifyD :: Demand -> Demand -> M ()
unifyD = undefined

type Constr = String
-- | Demands for absence analysis
data Demand
  = Var :-> Demand -- ^ Function call demand
  | Constructor Constr [Demand] -- ^ Tuple whose fields have demands
  | DApp Demand Demand
  | DRef Var
  | Ors [Demand]
  | Ands [Demand]
  | Unify Demand Demand
  deriving (Eq, Ord, Show, Data)

top = Ands []
bot = Ors []
type Env = M.Map Var Demand

unify :: (MonadState Env m, MonadVar m, Alternative m) => Demand -> Demand -> m Demand
unify (DRef a) b = do
  gets (M.!? a) >>= \case
    Nothing -> modify (M.insert a b) >> pure b
    Just a' -> unify a' b
unify b (DRef a) = do
  gets (M.!? a) >>= \case
    Nothing -> modify (M.insert a b) >> pure b
    Just a' -> unify b a'
unify (Ors ls) r = do
    l <- asum (map pure ls)
    unify l r
unify l (Ors rs) = do
    r <- asum (map pure rs)
    unify l r
unify l (Ands rs) = do
   let (as,bs) = splitUnifies rs
   mapM_ (uncurry unify) as
   bs' <- traverse (unify l) bs
   pure (Ands bs')
unify (Ands ls) r = do
   let (as,bs) = splitUnifies ls
   mapM_ (uncurry unify) as
   bs' <- traverse (`unify` r) bs
   pure (Ands bs')
unify (l :-> le) (r :-> re) = do
   v <- unify (DRef l) (DRef r)
   let
     o = case v of
      DRef v' -> v'
      _ -> undefined
   e <- unify le re
   pure (o :-> e)
unify (Constructor l ls) (Constructor r rs) = do
   guard (l == r)
   let os = zipWith (&&&) ls rs
   pure (Constructor l os)
unify (DApp f arg) e = do
    mkCall f arg >>= \case
      Just o -> unify o e
      Nothing -> pure $ Unify (DApp f arg) e
unify e (DApp f arg) = do
    mkCall f arg >>= \case
      Just o -> unify e o
      Nothing -> pure $ Unify e (DApp f arg)
unify _ _ = empty

substDemand :: Var -> Demand -> Demand -> Demand
substDemand v sub = runT' (
   tryTrans_ \case
     DRef v' | v == v' -> Just sub
     _ -> Nothing
  ||| recurse)


resolve :: (MonadState Env m) => Demand -> m Demand
resolve (DRef v) = gets (M.!? v) >>= \case
  Nothing -> pure (DRef v)
  Just o -> resolve o
resolve (DApp f a) = fromMaybe (DApp f a) <$> mkCall f a
resolve a = pure a
mkCall :: (MonadState Env m) => Demand -> Demand -> m (Maybe Demand)
mkCall f arg = do
    resolve f >>= \case
      (l :-> r) -> pure $ Just $ substDemand l r arg
      _ -> pure Nothing



splitUnifies :: [Demand] -> ([(Demand, Demand)],[Demand])
splitUnifies ls = partitionEithers [ case x of
  Unify a b -> Left (a,b)
  _ -> Right x
  | x <- ls]

-- normalize :: Demand -> Demand
-- normalize 
normalformDemand :: Demand -> [Demand]
normalformDemand (Ands ls) = Ands <$> traverse normalformDemand ls
normalformDemand (Ors ls) = concatMap normalformDemand ls
normalformDemand (Unify a b) = Unify <$> normalformDemand a <*> normalformDemand b
normalformDemand (a :-> b) = (a :->) <$> normalformDemand b
normalformDemand a = [a]

-- -- | Merge sequential demands
-- join :: Demand -> Demand -> Demand
-- join Absent d = d
-- join d Absent = d
-- join Used _ = Used
-- join _ Used = Used
-- join (ListD d1) (ListD d2) = ListD (join d1 d2)
-- join (TupleD ds1) (TupleD ds2) = TupleD (zipWith join ds1 ds2)
-- join _ _ = error "join: incompatible demands"


-- type Ana l = l -> Demand -> (DemandEnv, )
-- absenceAna :: Expr 

