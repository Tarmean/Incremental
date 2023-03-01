{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
-- | This module analyses if/how often identifiers are used, and does inling
module Analysis where


import OpenRec
import qualified Data.Map.Strict as M
import qualified Data.Map as LM
import CompileQuery
import Data.Foldable (Foldable(foldl'))
import Data.Data (Data)
import GHC.Stack (HasCallStack)
import Prettyprinter (Pretty (pretty), align)
import Data.Coerce (coerce)
import qualified Data.Set as S
import Data.Bifunctor (second)
import Data.Functor.Identity (Identity(runIdentity))
import Data.Maybe (fromMaybe)


-- | Composes a recursive analysis
-- - What are the results for all terms?
-- - What other terms does the current one refer to?
--
-- We search a fixpoint @f(e) + sum(f(t) for t in free_vars(e))@
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
analyzeArity tl=  MonoidMap (M.insert (unSource $ root tl) Many $ recs M.! unSource (root tl))
  where
    defUsage = M.mapKeys unSource $ M.map calcUsage (defs tl)
    -- if top-level definitions refer to each other, calculate ther fixpoint
    recs = fixTransitive @_ @Usage (coerce defUsage)
    -- calculate usage for a single definition
    -- recurse` sums up the usage of each child term
    calcUsage = runQ 
     (   tryQuery_ \case
          (Ref  v::Expr) -> Just (singleton v Once)
          _ -> Nothing
     ||| tryQuery_ \case
          (LRef v::Lang) -> Just (singleton v Once)
          _ -> Nothing
     ||| tryQuery (\rec -> \case
          -- For `let v e in b`
          -- If `v` doesn't occur in `b`, we can skip visiting `e`.
          -- Later, it will be dropped anyway out.
          (Let v e body::OpLang) -> 
            let body' = rec body
            in case lookupMult v body' of
              None -> Just body'
              _ -> Just (body' <> rec e)
          _ -> Nothing)
     ||| recurse)

singleton :: k -> v -> MonoidMap k v
singleton k v = MonoidMap (M.singleton k v)

lookupMult :: (Monoid v, Ord k) => k -> MonoidMap k v -> v
lookupMult k (MonoidMap m) = M.findWithDefault mempty k m
(\\) :: Ord k => MonoidMap k v -> k -> MonoidMap k v
(\\) (MonoidMap m) v = MonoidMap $ M.delete v m

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



simpleBinds :: M.Map Source Lang -> M.Map Source Lang 
simpleBinds env = M.filterWithKey (\k _ ->  simples M.! k) env
  where
    simples = LM.mapWithKey isSimple env
    envCount = LM.map (outMultiplicity envCount) env
    isSimple _ (OpLang Opaque{}) = True
    isSimple k (OpLang (HasType _ s _)) = isSimple k s
    isSimple _ (LRef k) = simples LM.! Source k
    isSimple k _ = M.findWithDefault Many k envCount == Once
    

withArity :: Usage -> MonoidMap Var Usage -> [Var]
withArity us (MonoidMap m) = map fst . filter ((==us) . snd) $ M.toList m


dropUseless :: MonoidMap Var Usage -> TopLevel -> TopLevel
dropUseless arities tl = tl {
    defs = M.filterWithKey (\k _ -> S.notMember (unSource k) useless) (defs tl)
 }
  where
    useless = S.fromList $ withArity None arities

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


inlineLang :: S.Set Var -> M.Map Var Lang -> Lang -> Lang
inlineLang toInline m = runIdentity .: runT $
  tryTrans_ @Lang (\case
    LRef v
      | S.member v toInline -> Just $ fromMaybe (error "Missing def") (m M.!? v)
    _ -> Nothing)
  ||| recurse


doInlines :: MonoidMap Var Usage -> TopLevel -> TopLevel
doInlines arities tl = tl {
    defs = M.filterWithKey (\k _ -> unSource k `S.notMember` inlines) defs'
 }
  where
    defs' = M.map (second (inlineLang inlines (M.mapKeysMonotonic unSource $ M.map snd defs'))) (defs tl)
    inlines = gatherInlines tl arities defs'
gatherInlines :: TopLevel -> MonoidMap Var Usage -> M.Map Source ([Var], Lang) -> S.Set Var
gatherInlines tl arities theDefs = S.union simples inlines
  where
    toInline = withArity Once arities
    avoids = avoidInline (defs tl)
    inlines = S.fromList [ v | v <- toInline, S.notMember v avoids, Just (_args, def) <- [theDefs M.!? Source v], inlinable def]
    simples = S.fromList $ map unSource $ M.keys $ simpleBinds (M.map snd $  defs tl)

inlinable :: Lang -> Bool
-- inlinable (Comprehend {}) = True
-- inlinable (Return {}) = True
inlinable (OpLang Fold{}) = False
inlinable _ = True

-- | Count how many results are produced by a query
outMultiplicity :: M.Map Source Usage -> Lang -> Usage
outMultiplicity _ (Return _) = Once
outMultiplicity env (Bind l _ b) = outMultiplicity env l .* outMultiplicity env b
outMultiplicity env (Filter _ f) = outMultiplicity env f
outMultiplicity env (LRef f) = M.findWithDefault Many (Source f) env
outMultiplicity env (AsyncBind _ a) = outMultiplicity env a
outMultiplicity env (OpLang l) = case l of
  Opaque {} -> Many
  Union a b -> outMultiplicity env a <> outMultiplicity env b
  Unpack _ _ b -> outMultiplicity env b
  Let _ _ b -> outMultiplicity env b
  Fold {} -> Once
  Call _ -> Once
  Force (Thunk t _) -> M.findWithDefault Many t env
  HasType _ t _ -> outMultiplicity env t
  Distinct t -> outMultiplicity env t


optPass :: TopLevel -> TopLevel
optPass tl = dropUseless multiplicities $ doInlines multiplicities $ dropUseless multiplicities tl
  where
    multiplicities = analyzeArity tl

dropUnused :: MonoidMap Var Usage -> TopLevel -> TopLevel
dropUnused m tl = tl {
    defs = out
 }
  where
    unused = S.fromList $ withArity None m
    isUnused x = x `S.member` unused || M.notMember x (unMonoidMap m)
    out = M.filterWithKey (\k _ -> not $ isUnused (unSource k)) (defs tl)


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
