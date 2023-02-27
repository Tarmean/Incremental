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
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE OverloadedStrings #-}
module DemandAnalysis  where
import CompileQuery
import Data.Data (Data)
import qualified Data.Map.Strict as M
import Prettyprinter



data Demand = Tup [Demand] | NoInfo | NoneUsed | Each Demand deriving (Eq, Ord, Show, Data)
each :: Demand -> Demand
each NoInfo = NoInfo
each NoneUsed = NoneUsed
each d = Each d
tup :: [Demand] -> Demand
tup ls
  | all (== NoInfo) ls = NoInfo
  | all (== NoneUsed) ls = NoneUsed
  | otherwise = Tup ls


class Lattice a where
  (/\) :: a -> a -> a
  (\/) :: a -> a -> a

instance Lattice Demand where
    (/\) :: Demand -> Demand -> Demand
    (/\) NoneUsed a = a
    (/\) a NoneUsed = a
    (/\) (Each a) (Each b) = each (a /\ b)
    (/\) NoInfo _ = NoInfo
    (/\) _ NoInfo = NoInfo
    (/\) (Tup a) (Tup b) = tup (zipWith (/\) a b)
    (/\) _ _ = error "Invalid demand pair"

    (\/) :: Demand -> Demand -> Demand
    NoneUsed \/ NoneUsed = NoneUsed
    (\/) (Tup a) (Tup b) = tup (zipWith (\/) a b)
    (\/) (Tup a) NoneUsed = tup (map (NoneUsed \/) a)
    (\/) NoneUsed (Tup a) = tup (map (NoneUsed \/) a)
    (\/) (Each a) (Each b) = each (a /\ b)
    (\/) NoneUsed (Each b) = each (NoneUsed \/ b)
    (\/) (Each b) NoneUsed = each (NoneUsed \/ b)
    _ \/ _ = NoInfo



fixDemands :: TopLevel -> GlobalEnv
fixDemands (TopLevel defs _root) = fixOut demands0
  where
    demands0 = GlobalEnv $ M.fromList [(k,replicate (length args) NoneUsed) | (k,(args, _)) <- M.toList defs, not (null args)]


    fixOut env
      | env == env' = env
      | otherwise = fixOut env'
      where env' = fixOut1 env
    fixOut1 :: GlobalEnv -> GlobalEnv
    fixOut1 demandEnv = GlobalEnv $ flip M.mapWithKey (globalEnv demandEnv) $ \k _ ->
        let
            (args, body) = defs M.! k
            DemandEnv dmd = calcDemandL demandEnv NoInfo body
        in [M.findWithDefault NoneUsed arg dmd | arg <- args]



newtype DemandEnv = DemandEnv { demandEnv :: M.Map Var Demand }
  deriving (Eq,Ord,Show)

instance Pretty Demand where
   pretty NoneUsed = "0"
   pretty (Each a) = "[" <> pretty a <> "]"
   pretty (Tup a) = tupled (map pretty a)
   pretty NoInfo = "?"

instance Pretty GlobalEnv where
   pretty (GlobalEnv m) = "GlobalEnv" <+> braces (vsep (map (\(k,v) -> pretty k <+> "->" <+> pretty v) (M.toList m)))
newtype GlobalEnv = GlobalEnv { globalEnv :: M.Map Source [Demand] }
  deriving (Eq,Ord,Show)

analyseCall :: GlobalEnv -> Thunk -> DemandEnv
analyseCall env (Thunk src args) = case M.lookup src (globalEnv env) of
    Just demands -> DemandEnv (M.fromList (zip args demands))
    Nothing -> DemandEnv (M.fromList (map (,NoInfo) args))

instance Lattice DemandEnv where
    (/\) :: DemandEnv -> DemandEnv -> DemandEnv
    (/\) (DemandEnv a) (DemandEnv b) = DemandEnv (M.unionWith (/\) a b)

    (\/) :: DemandEnv -> DemandEnv -> DemandEnv
    (\/) (DemandEnv a) (DemandEnv b) = DemandEnv (M.intersectionWith (\/) a b)

botEnv :: DemandEnv
botEnv = DemandEnv mempty

calcDemand :: GlobalEnv -> Demand -> Expr -> DemandEnv
calcDemand _ NoneUsed _ = botEnv
calcDemand _ dmd (Ref v) = DemandEnv (M.singleton v dmd)
calcDemand g dmd (Proj idx total ex) = calcDemand g dmd' ex
  where
    leftOf = idx
    rightOf = total-idx-1
    dmd' = tup (replicate leftOf NoneUsed ++ [dmd] ++ replicate rightOf NoneUsed)
calcDemand g dmd (Slice offset len total ex) = calcDemand g dmd' ex
  where
    leftOf = offset
    rightOf = total-offset-len
    inner = case dmd of
      Tup ds -> ds
      NoInfo -> replicate len NoInfo
      Each _ -> error "projection on list"
    dmd' = tup (replicate leftOf NoneUsed ++ inner ++ replicate rightOf NoneUsed)
calcDemand g dmd (Tuple _ ls) = foldr1 (/\) (zipWith (calcDemand g) dmds ls)
  where
    dmds = case dmd of
      Tup ds -> ds
      NoInfo -> NoInfo <$ ls
      Each _ -> error "projection on list"
calcDemand g dmd (BOp _ l r) = calcDemand g dmd l /\ calcDemand g dmd r
calcDemand _ _ Unit = botEnv
calcDemand g _ (AThunk t) = analyseCall g t
calcDemand g _ (Aggr _ t) = analyseCall g t
calcDemand g _ (AggrNested _ t) = calcDemandL g NoInfo t
calcDemand g _ (Nest t) = calcDemandL g NoInfo t
calcDemand g d (HasEType _ e _) = calcDemand g d e
calcDemand _ _ (Lit {}) = botEnv
calcDemand _ _ (Lookup {}) = error "Lookup should not exist yet during demand analysis; not implemented"


calcDemandL :: GlobalEnv -> Demand -> Lang -> DemandEnv
calcDemandL _ NoneUsed _ = botEnv
calcDemandL g d (Bind bhead var bod) = bodEnv /\ headEnv
  where
    bodEnv = calcDemandL g d bod
    bodDemand = maybe NoneUsed each $ M.lookup var (demandEnv bodEnv)
    headEnv = calcDemandL g bodDemand bhead
calcDemandL g d (Filter p b) = calcDemand g d p /\ calcDemandL g d b
calcDemandL g d (Return b) = case d of
    Each dmd -> calcDemand g dmd b
    _ -> calcDemand g NoInfo b
calcDemandL _ d (LRef b) = DemandEnv (M.singleton b d)
calcDemandL g d (AsyncBind ls b) = foldr1 (/\) [analyseCall g t | (_,_,t) <- ls] /\ calcDemandL g d b
calcDemandL g d (OpLang l) = calcDemandOL g d l


calcDemandOL :: GlobalEnv -> Demand -> OpLang -> DemandEnv
calcDemandOL _ _ (Opaque {}) = botEnv
calcDemandOL g d (Union l r) = calcDemandL g d l /\ calcDemandL g d r
calcDemandOL g d (Let v exprHead bod) = bodEnv /\ headEnv
  where
    bodEnv = calcDemandL g d bod
    headDemand = maybe NoneUsed each $ M.lookup v (demandEnv bodEnv)
    headEnv = calcDemand g headDemand exprHead
calcDemandOL g d (Call t) = calcDemand g d t
calcDemandOL g _ (Force t) = analyseCall g t
calcDemandOL g d (Distinct t) = calcDemandL g d t
calcDemandOL g d (Group kl vl _ t) = calcDemandL g (headDemand /\ d) t
  where headDemand = each (tup (replicate kl NoInfo ++ replicate vl NoneUsed))
calcDemandOL g d (HasType _ t _) = calcDemandL g d t
calcDemandOL g d (Unpack uHead uBound bod) = envBod /\ calcDemand g (mkProjEnv envBod) uHead
  where
    envBod = calcDemandL g d bod
    mkProjEnv :: DemandEnv -> Demand
    mkProjEnv env = tup $ do
        m <- uBound
        case m of
          Nothing -> [NoneUsed]
          Just v -> case M.lookup v (demandEnv env) of
            Just dmd -> [dmd]
            Nothing -> [NoneUsed]

