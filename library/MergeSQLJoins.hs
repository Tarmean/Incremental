{-# LANGUAGE OverloadedRecordDot #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}
-- | If we join a GROUP BY query with other queries, we can move linear joins into the groupby
--
-- Similarly for limit/offset and order by
module MergeSQLJoins where
import SQL
import FundepAnalysis (toGraph, NId (..))
import WatchlistPropagator (reachable)
import qualified Data.Set as S
import OpenRec
import Control.Monad.Writer
import Data.Data (Data)
import Control.Lens
import Data.Generics.Labels ()
import qualified Data.Map.Strict as M
import Data.Maybe (listToMaybe, maybeToList)
import CompileQuery (Var)
import Util (prettyS)


mergeGroupBys :: Data a => a -> a
mergeGroupBys = runT' (recurse >>> tryTrans_ mergeGroupBys1)



mergeableWithLinearJoin :: SQL -> Maybe (SQL, (forall a. Data a => a -> a) -> SQL -> SQL)
mergeableWithLinearJoin (GroupQ s a) = Just (a, \f -> GroupQ (f s))
mergeableWithLinearJoin (Slice lim off a) = Just (a, \_ -> Slice lim off)
mergeableWithLinearJoin _ = Nothing


mergeGroupBys1 :: SPJ -> Maybe SPJ
mergeGroupBys1 s = listToMaybe $ do
   (k,mergeableWithLinearJoin -> Just (j, recon)) <- s.sources
   let
     graph = toGraph (ASPJ s)
     dominated
       =
       [ (k',q)
       | (k',q) <- s.sources
       , k' /= k
       , reachable graph [ARef k] (ARef k')
       ]
     innerSources = S.fromList (map fst dominated)
     isOtherSource k' = not (S.member k' innerSources)
     dropK (a,b)
       | a == k = (k,ASPJ $ SPJ mempty mempty mempty)
       | otherwise = (a,b)
     leftover = s { sources = map dropK $ filter (isOtherSource . fst) s.sources }

     (leftover', frees) = renameRefs innerSources k leftover
   guard $ not (S.null innerSources)
   j' <- maybeToList $ mapSPJ (\spj ->
       spj
       & #proj <>~ M.fromList [ (f', Ref r f) | (r,f,f') <- S.toList frees]
       & #sources <>~ substSQL k spj.proj dominated) j
   pure leftover' { sources = updateAt k (recon id j') leftover'.sources }

updateAt :: Ord k => k -> v -> [(k, v)] -> [(k,v)]
updateAt k v ls = do
  (k',v') <- ls
  if k == k' then [(k,v)] else [(k',v')]


renameRefs :: Data a => S.Set Var -> Var -> a -> (a, S.Set (Var, AField, AField))
renameRefs innerSources k = 
    runWriter . runT (
           tryTransM_  \case
             Ref v field | v `S.member` innerSources -> Just $ do
               let renamedField = field <> "_" <> prettyS v
               tell (S.singleton (v,field, renamedField))
               pure (Ref k renamedField)
             _ -> Nothing
          ||| recurse
            )
