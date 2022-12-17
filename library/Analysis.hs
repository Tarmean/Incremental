{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
module Analysis where


import OpenRec
import qualified Data.Map.Strict as M
import CompileQuery
import Data.Foldable (Foldable(foldl'))
import Data.Data (Data)
import GHC.Stack (HasCallStack)
import Prettyprinter (Pretty (pretty), align)
import Data.Coerce (coerce)
import qualified Data.Set as S
import Data.Bifunctor (second)
import Data.Functor.Identity (Identity(runIdentity))


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


analyzeArity :: TopLevel -> MonoidMap Var Usage
analyzeArity tl=  MonoidMap (recs M.! unSource (root tl))
  where
    defUsage = M.mapKeys unSource (M.map theQ (defs tl))
    recs = fixTransitive @_ @Usage $ coerce defUsage
    theQ = runQ $
      query (\rec -> \case
        (Ref  v::Expr) -> MonoidMap (M.singleton v Once)
        a -> rec a)
     |||
      query (\rec -> \case
        (LRef v::Lang) -> MonoidMap (M.singleton v Once)
        a -> rec a )
     ||| recurse
avoidInline :: Data a => a -> S.Set Var
avoidInline = runQ $ 
   tryQuery (\_rec -> \case
       (Return a::Lang) -> Just (freeVarsQ a)
       _ -> Nothing)
   ||| recurse

(!!!) :: (HasCallStack, Ord k, Show k, Show a) => M.Map k a -> k -> a
m !!! k = case M.lookup k m of
  Nothing -> error $ "Key not found: " ++ show k ++ ", in map: " ++ show m
  Just o -> o


simpleBind :: Lang -> Bool
simpleBind (Return _) = True
simpleBind (Bind _ b (Return c))
  | Ref b == c = True
simpleBind _ = False

-- simpleBinds :: TopLevel -> [Source]
simpleBinds :: M.Map b (a, Lang) -> [b]
simpleBinds def = map fst . filter (simpleBind . snd . snd) $ M.toList def

withArity :: Usage -> MonoidMap Var Usage -> [Var]
withArity us (MonoidMap m) = map fst . filter ((==us) . snd) $ M.toList m


dropUseless :: MonoidMap Var Usage -> TopLevel -> TopLevel
dropUseless arities tl = tl {
    defs = M.filterWithKey (\k _ -> S.notMember (unSource k) useless) (defs tl)
 }
  where
    useless = S.fromList $ withArity None arities

localsFor :: [(Var, Typed Var)] -> Var -> [Var]
localsFor binds v 
  | null out = [] -- error ("No locals for " ++ show v ++ " in " ++ show binds)
  | otherwise = out
  where out = [localN | (localN,globalN) <- binds, tyData globalN == v]

inlineComp :: Lang -> Var -> Lang -> Lang
inlineComp a _ _ = a
-- inlineComp (Comprehend {..}) v (Return r)
--   = Comprehend { cLet = cLet ++ newLet, .. }
--   where
--     locals = localsFor cBound v
--     newLet
--      = if null locals 
--        then [(v,r)]
--        else [(v',r) | v' <- locals]
-- inlineComp l@Comprehend{} var r@Comprehend{} = Comprehend {
--     cBound = cBound l <> cBound r,
--     cPred = cPred l <> cPred r,
--     cPred2 = cPred2 l <> cPred2 r,
--     eTyp = mergeTyp (eTyp l) (mergeTyp r),
--     cLet = cLet l <> cLet r <> [(var', cOut r) | var' <- notNull $ localsFor (cBound l) var],
--     cOut = cOut l
--   }
--   where
--     notNull [] = error "localsFor returned empty list"
--     notNull xs = xs
-- inlineComp _ _ _ = error "Illegal merge"

mergeTyp :: p1 -> p2 -> p1
mergeTyp a _ = a


inlineLang :: M.Map Var Lang -> Lang -> Lang
inlineLang m = runIdentity .: runT $
  trans @Lang (\rec -> \case
    LRef v
      | Just o <- m M.!? v -> pure o
    a -> rec (a::Lang))
  ||| recurse


doInlines :: MonoidMap Var Usage -> TopLevel -> TopLevel
doInlines arities tl = tl {
    defs = M.filterWithKey (\k _ -> unSource k `M.notMember` inlines) defs'
    -- funs = M.map (inlineLang inlines) (funs tl)
 }
  where
    defs' = M.map (second (inlineLang inlines)) (defs tl)
    inlines = gatherInlines tl arities defs'
gatherInlines :: TopLevel -> MonoidMap Var Usage -> M.Map Source ([Var], Lang) -> M.Map Var Lang
gatherInlines tl arities theDefs = inlines
  where
    toInline = simples <> withArity Once arities
    avoids = avoidInline (defs tl)
    inlines = M.fromList [ (v, def) | v <- toInline, S.notMember v avoids, Just (_args, def) <- [theDefs M.!? Source v]]
    simples = unSource <$> simpleBinds (defs tl)

inlinable :: Lang -> Bool
-- inlinable (Comprehend {}) = True
-- inlinable (Return {}) = True
inlinable _ = True


optPass :: TopLevel -> TopLevel
optPass tl = doInlines multiplicities $ dropUseless multiplicities tl
  where multiplicities = analyzeArity tl
