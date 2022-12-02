{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecordWildCards #-}
module Analysis where


import OpenRec
import qualified Data.Map.Strict as M
import CompileQuery
import Data.Foldable (Foldable(foldl'))
import Data.Data (Data)
import GHC.Stack (HasCallStack)
import Prettyprinter (Pretty (pretty))
import Control.Monad.Identity (Identity(Identity))
import Data.Coerce (coerce)
import Data.Text.Prettyprint.Doc (align)
import qualified Data.Set as S
import Debug.Trace (traceShow)
import Test (testQ, testFlat)


newtype MonoidMap k v = MonoidMap { unMonoidMap :: M.Map k v }
  deriving (Show, Eq, Ord, Data)
instance (Ord k, Semigroup v) => Semigroup (MonoidMap k v) where
  MonoidMap a <> MonoidMap b = MonoidMap $ M.unionWith (<>) a b
instance (Ord k, Semigroup v) => Monoid (MonoidMap k v) where
  mempty = MonoidMap M.empty

instance (Pretty k,Pretty v) => Pretty  (MonoidMap k v) where
  pretty (MonoidMap m) = pretty "fromList" <> align (pretty (M.toList m))
-- Collect usage info for var binders.
class Monoid a => Mult a where
  -- | `mone` is identity, `mempty` is zero
  -- Distributes over `mappend`
  infixl 7 .*
  (.*) :: a -> a -> a
  mone :: a

class Monoid a => Alt a where
  -- | forms a lattice with mone as top and mempty as bottom
  -- Distributes over `mappend`
  infixr 5 .||
  (.||) :: a -> a -> a
instance Alt Usage where
  (.||) = max

instance (Ord k, Alt v) => Alt (MonoidMap k v) where
   (.||) (MonoidMap a) (MonoidMap b) = MonoidMap $   M.unionWith (.||) a b

transitive1 :: (Show k, Show a, HasCallStack, Ord k,Alt a, Mult a) => M.Map k (M.Map k a) -> M.Map k a -> M.Map k a
transitive1 m direct = out
  where
    out = unMonoidMap $ MonoidMap direct <> indirect
    indirect = foldl' (<>) mempty [MonoidMap $ M.map (v .*) (M.findWithDefault mempty k' m) | (k',v) <- M.toList direct]


transitive :: (Show k, Show a, HasCallStack, Ord k, Alt a, Mult a) => M.Map k (M.Map k a) -> M.Map k (M.Map k a) -> M.Map k (M.Map k a)
transitive m0 m = M.mapWithKey (\k _ ->transitive1 m (m0 M.! k)) m

fixTransitive :: (Show k, Show a, HasCallStack, Ord k, Mult a, Alt a, Eq a) => M.Map k (M.Map k a) -> M.Map k (M.Map k a)
fixTransitive m0 = go m0

  where
    go m
      | m' == m = m 
      | otherwise = go m'
      where  m' = transitive m0 m

data Usage = None | Once | Many
  deriving (Eq, Ord, Show)
instance Pretty Usage where
  pretty s = pretty (show s)
instance Semigroup Usage where
  None <> x = x
  x <> None = x
  _ <> _ = Many
instance Monoid Usage where
  mempty = None
instance Mult Usage where
    mone = Once
    None .* _ = None
    _ .* None = None
    Once .* Once = Once
    _ .* _ = Many

type Usages = M.Map Var Usage

(<&>) :: (Ord k, Semigroup a) => M.Map k a -> M.Map k a -> M.Map k a
(<&>) = M.unionWith (<>)


analyzeArity :: Data a => a -> MonoidMap Var Usage
analyzeArity = runQ $
  query (\rec -> \case
    Ref @Var v -> MonoidMap (M.singleton (tyData v) Once)
    a -> rec a)
 &&&
  query (\rec -> \case
    (c@Comprehend {..}::Lang' Var) -> 
      MonoidMap (M.fromListWith (<>) [ (tyData v, Once) | (_,v) <- cBound ])
    a -> rec a )
 &&&
  query (\rec' (TopLevel {..}::TopLevel) ->
      let
        rec :: Data a => a -> MonoidMap Var Usage
        rec = rec' . Identity
        defUsage = M.mapKeys unSource (M.map rec defs)
        funUsage = M.mapKeys unFun (M.map rec funs)
        recs = fixTransitive @_ @Usage $ coerce (defUsage <>  funUsage)
      in MonoidMap (recs M.! unSource root))
 &&& recurse

(!!!) :: (HasCallStack, Ord k, Show k, Show a) => M.Map k a -> k -> a
m !!! k = case M.lookup k m of
  Nothing -> error $ "Key not found: " ++ show k ++ ", in map: " ++ show m
  Just o -> o

tester = do
  let tl = toTopLevel testFlat
  let !mults  = analyzeArity tl
  pprint $ M.toList $ gatherInlines mults tl


simpleBind :: Lang' Var -> Bool
simpleBind (Comprehend [(a,_)] [] [] [] _ (Ref c))
  | tyData c == a = True
simpleBind _ = False

simpleBinds :: TopLevel -> [Source]
simpleBinds (TopLevel {..}) = map fst . filter (simpleBind .snd) $ M.toList defs

withArity :: Usage -> MonoidMap Var Usage -> [Var]
withArity us (MonoidMap m) = map fst . filter ((==us) . snd) $ M.toList m


dropUseless :: MonoidMap Var Usage -> TopLevel -> TopLevel
dropUseless arities tl = tl {
    defs = M.filterWithKey (\k _ -> S.notMember (unSource k) useless) (defs tl),
    funs = M.filterWithKey (\k _ -> S.notMember (unFun k) useless) (funs tl)
 }
  where
    useless = S.fromList $ withArity None arities

inlineComp :: Lang -> Var -> Lang -> Lang
inlineComp (Comprehend {..}) v (Return r)
  = Comprehend { cLet = cLet ++ [(v,r)], .. }
inlineComp l@Comprehend{} var r@Comprehend{} = Comprehend {
    cBound = cBound l <> cBound r,
    cPred = cPred l <> cPred r,
    cPred2 = cPred2 l <> cPred2 r,
    eTyp = mergeTyp (eTyp l) (mergeTyp r),
    cLet = cLet l <> cLet r <> [(var, cOut r)],
    cOut = cOut l
  }
inlineComp _ _ _ = error "Illegal merge"

mergeTyp :: p1 -> p2 -> p1
mergeTyp a _ = a


inlineLang :: M.Map Var Lang -> Lang -> Lang
inlineLang binds c@Comprehend {} = inlined
  where
    relevant = S.fromList $ filter (`M.member` binds) $ map (tyData . snd) $ cBound c
    c' = c { cBound = filter ((`S.notMember` relevant) . tyData . snd) $ cBound c }
    inlined = foldl' (uncurry . inlineComp) c' [ (v, binds !!! v) | v <- S.toList relevant ]
inlineLang _ a = a

doInlines :: MonoidMap Var Usage -> TopLevel -> TopLevel
doInlines arities tl = tl {
    defs = M.filterWithKey (\k _ -> unSource k `M.notMember` inlines) $ M.map (inlineLang inlines) (defs tl)
    -- funs = M.map (inlineLang inlines) (funs tl)
 }
  where inlines = gatherInlines arities tl
gatherInlines :: Show a => MonoidMap Var Usage -> TopLevel' a -> M.Map Var a
gatherInlines arities tl = inlines
  where inlines = M.fromList [ (v, def) | v <- withArity Once arities, Just def <- [defs tl M.!? Source v]]

optPass :: TopLevel -> TopLevel
optPass tl = doInlines multiplicities $ dropUseless multiplicities tl
  where multiplicities = analyzeArity tl
-- inlineUnique
-- multUsages :: M.Map Var Usages -> Var -> M.Map Var Usage
-- multUsages us = [ (v, ms)  | (v, ms) <- M.toList us, (ve, m) <- M.toList ms ]

-- anaUsage :: 
