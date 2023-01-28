{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
-- | In a Data.Data traversal, we want to visit a `target` set of types.
-- For every type reachable from a `source` value, cache whether it contains a `target.`
-- Adopted from the Lens package for multiple target types
module HitTest where
import Data.Data

import qualified Data.Proxy as X (Proxy (..))
import qualified Data.Typeable as X (typeRep)
import qualified Data.HashSet as S
import Data.HashSet (HashSet)
import Data.HashMap.Strict (HashMap, (!))
import qualified Data.HashMap.Strict as M
import GHC.IO (IO(..), unsafePerformIO)
import Data.IORef
import qualified Control.Exception as E
import Data.Maybe (fromMaybe)
import GHC.Base (realWorld#)

-------------------------------------------------------------------------------
-- Data Box
-------------------------------------------------------------------------------

data DataBox = forall a. Data a => DataBox
  { dataBoxKey :: TypeRep
  , _dataBoxVal :: a
  }

{-# INLINE typeRepOf #-}
typeRepOf :: forall a. Typeable a => TypeRep
typeRepOf = typeRep (X.Proxy @a)
dataBox :: forall a. Data a => a -> DataBox
dataBox = DataBox (typeRepOf @a)
{-# INLINE dataBox #-}

-- partial, caught elsewhere
sybChildren :: Data a => a -> [DataBox]
sybChildren x
  | isAlgType dt = do
    c <- dataTypeConstrs dt
    -- FIXME: This throws for strict constructors
    -- which probably makes this strictly worse than using the constr information directly
    gmapQ dataBox (fromConstr c `asTypeOf` x)
  | otherwise = []
  where dt = dataTypeOf x
{-# INLINE sybChildren #-}

-------------------------------------------------------------------------------
-- HitMap
-------------------------------------------------------------------------------

type HitMap = HashMap TypeRep (HashSet TypeRep)

emptyHitMap :: HitMap
emptyHitMap = M.fromList
  [ (tRational, S.singleton tInteger)
  , (tInteger,  S.empty)
  ] where
  tRational = X.typeRep (X.Proxy :: X.Proxy Rational)
  tInteger  = X.typeRep (X.Proxy :: X.Proxy Integer )

insertHitMap :: DataBox -> HitMap -> HitMap
insertHitMap box hit = fixEq trans (populate box) `mappend` hit where
  populate :: DataBox -> HitMap
  populate a = f a M.empty where
    f (DataBox k v) m
      | M.member k hit || M.member k m = m
      | cs <- sybChildren v = fs cs $ M.insert k (S.fromList $ map dataBoxKey cs) m
    fs []     m = m
    fs (x:xs) m = fs xs (f x m)

  trans :: HitMap -> HitMap
  trans m = M.map f m where
    f x = x `mappend` foldMap g x
    g x = fromMaybe (hit ! x) (M.lookup x m)

fixEq :: Eq a => (a -> a) -> a -> a
fixEq f = go where
  go x | x == x'   = x'
       | otherwise = go x'
       where x' = f x
{-# INLINE fixEq #-}

-- | inlineable 'unsafePerformIO'
inlinePerformIO :: IO a -> a
inlinePerformIO (IO m) = case m realWorld# of
  (# _, r #) -> r
{-# INLINE inlinePerformIO #-}

data Cache = Cache HitMap (HashMap TypeRep (HashMap (HashSet TypeRep) (Maybe Follower)))

cache :: IORef Cache
cache = unsafePerformIO $ newIORef $ Cache emptyHitMap M.empty
{-# NOINLINE cache #-}

readCacheFollower :: DataBox -> S.HashSet TypeRep -> Maybe Follower
readCacheFollower b@(DataBox kb _) ka = inlinePerformIO $
  readIORef cache >>= \ (Cache hm m) -> case M.lookup kb m >>= M.lookup ka of
    Just a -> return a
    Nothing -> E.try (return $! insertHitMap b hm) >>= \case
      Left err@E.SomeException{}                         -> error (show err <>", in type " <> show kb) -- atomicModifyIORef cache $ \(Cache hm' n) -> (Cache hm' (insert2 kb ka Nothing n), Nothing)
      Right hm' | fol <- Just (follower kb ka hm') -> atomicModifyIORef cache $ \(Cache _ n) -> (Cache hm' (insert2 kb ka fol n),    fol)

insert2 :: TypeRep -> HashSet TypeRep -> a -> HashMap TypeRep (HashMap (HashSet TypeRep) a) -> HashMap TypeRep (HashMap (HashSet TypeRep) a)
insert2 x y v = M.insertWith (const $ M.insert y v) x (M.singleton y v)
{-# INLINE insert2 #-}

-------------------------------------------------------------------------------
-- Answers
-------------------------------------------------------------------------------

data Answer b
  = Hit TypeRep
  | Follow
  | Miss

-------------------------------------------------------------------------------
-- Oracles
-------------------------------------------------------------------------------

newtype Oracle = Oracle { fromOracle :: forall t. Typeable t => t -> Answer t }

hitTest :: forall a. (Data a) => a -> HashSet TypeRep -> Oracle
hitTest a b = Oracle $ \(c :: c) ->
  let tyA = typeOf c
  in
  if tyA `S.member` b
  then Hit tyA
  else case readCacheFollower (dataBox a) b of
        Just p | not (p (typeOf c)) -> Miss
        _ -> Follow

-------------------------------------------------------------------------------
-- Traversals
-------------------------------------------------------------------------------

-- biplateData :: forall f s a. (Applicative f, Data s) => (forall c. Typeable c => c -> Answer c a) -> (a -> f a) -> s -> f s
-- biplateData o f = go2 where
--   go :: Data d => d -> f d
--   go = gfoldl (\x y -> x <*> go2 y) pure
--   go2 :: Data d => d -> f d
--   go2 s = case o s of
--     Hit a  -> f a
--     Follow -> go s
--     Miss   -> pure s
-- {-# INLINE biplateData #-}

-- uniplateData :: forall f s a. (Applicative f, Data s) => (forall c. Typeable c => c -> Answer c a) -> (a -> f a) -> s -> f s
-- uniplateData o f = go where
--   go :: Data d => d -> f d
--   go = gfoldl (\x y -> x <*> go2 y) pure
--   go2 :: Data d => d -> f d
--   go2 s = case o s of
--     Hit a  -> f a
--     Follow -> go s
--     Miss   -> pure s
-- {-# INLINE uniplateData #-}

-------------------------------------------------------------------------------
-- Follower
-------------------------------------------------------------------------------

part :: (a -> Bool) -> HashSet a -> (HashSet a, HashSet a)
part p s = (S.filter p s, S.filter (not . p) s)
{-# INLINE part #-}

type Follower = TypeRep -> Bool

follower :: TypeRep -> HashSet TypeRep -> HitMap -> Follower
follower a b m
  | S.null hit               = const False
  | S.null miss              = const True
  -- | S.size hit < S.size miss = (`S.member` hit)
  | otherwise = \k -> not (S.member k miss)
  where
    (hit, miss) = part (\x -> not $ S.null (S.intersection b (m ! x))) (S.insert a (m ! a))
