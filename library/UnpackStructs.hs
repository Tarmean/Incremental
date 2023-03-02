{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- | Map nested structs to flat tuples, and projections to flat slices
module UnpackStructs where


import CompileQuery
import OpenRec
import qualified Data.Map.Strict as M
import Data.Data (Data)
import Data.Maybe (fromMaybe)


-- | Calculate how many columns a type consumes
widthOfType :: (Source -> Int) -> ExprType -> Int
widthOfType _ (EBase _) = 1
widthOfType env (TupleTyp t ls) 
 | isTupleTag t = sum (map (widthOfType env) ls)
 | otherwise = 1
widthOfType argCount (ListTy source _) = case source of
   SourceTy s -> argCount s
   RootTy -> 0
   _ -> error "Invalid listTy"
widthOfType _ e = error ("wrong kind in widthOfType: " <> prettyS e)

flattenType :: [ExprType] -> [ExprType]
flattenType ls = concatMap go ls
  where
    go (TupleTyp t ls) 
      | isTupleTag t = concatMap go ls
    -- FIXME: Probably should flatten thunks here
    go (ListTy _ _) = error "not implemented"
    go a = [a]

projToSlice :: (Source -> Int) -> Expr -> Maybe Expr
-- projToSlice _ (Proj 0 1 e) = Just $ e
projToSlice env (Proj field _total (HasEType _ expr (TupleTyp _ tys)))
  | resultIsTuple = Just (tryMergeSlice out)
  | otherwise = Just (tryMergeSlice $ Proj 0 1 out)
  where
    out = tryMergeSlice $ Slice offset width (length (flattenType tys)) expr
    (l,x) = case splitAt field tys of
        (l, x:_) -> (l,x)
        _ -> undefined
    offset = sum (map (widthOfType env) l)
    width = widthOfType env x
    resultIsTuple = case tys !! field of
      TupleTyp tag _ -> isTupleTag tag
      _ -> False
projToSlice _ _ = Nothing


unpackStructs :: TopLevel -> TopLevel
unpackStructs tl = runT' (recurse >>> tryTrans_ (projToSlice env)) tl
  where
    env x = length $ fst $ defs tl M.! x

mergeSlice :: Expr -> Maybe Expr
mergeSlice (Slice i _ total (Slice k l _ e)) = Just $ Slice (i+k) l total e
mergeSlice (Slice i _ total (Proj k _ e)) = Just $ Proj (i+k) total e
mergeSlice (Proj i _ (Slice off _ total e)) = Just $ Proj (i+off) total e
mergeSlice (Proj i _ (Tuple _ ls)) = Just $ ls !! i
mergeSlice _ = Nothing

sliceToTuple :: Expr -> Maybe Expr
-- sliceToTuple (Return (Slice k l t e)) = Just $ Return (tuple [Proj (k+i) t e | i <- [0..l-1]])
sliceToTuple (Slice k l t e) = Just $ (tuple [Proj (k+i) t e | i <- [0..l-1]])
sliceToTuple _ = Nothing

flattenTuple :: Expr -> Maybe Expr
flattenTuple (Tuple tag ls)
  | isTupleTag tag && any isTuple ls = Just $ tuple (concatMap flattenExprList ls)
  where
    isTuple (Tuple tag _) = isTupleTag tag
    isTuple (Slice {}) = True
    isTuple _ = False
flattenTuple _ = Nothing
flattenExprList :: Expr -> [Expr]
flattenExprList = go
  where
    go (Tuple tag ls)
      | isTupleTag tag = concatMap go ls
    go (Slice from to total ls) = [Proj i total ls | i <- [from..from+to-1]]
    go a = [a]

refToSlice  :: Expr -> Maybe Expr
refToSlice (HasEType _ (Ref r) (TupleTyp tag tys))
  | isTupleTag tag = Just $ Slice 0 width width (Ref r)
  where
    width = sum (map (widthOfType (const 0)) tys)
refToSlice _ = Nothing

dropTyp  :: Expr -> Maybe Expr
dropTyp (HasEType _ r _) = Just r
dropTyp _ = Nothing

mergeSlices :: Data a => a -> a
mergeSlices = runT' $ do
    block (recurse >>> (tryTrans_ refToSlice ||| tryTrans_ dropTyp ||| (tryTrans_ flattenTuple &&& tryTrans_ flattenLookupArgs &&& (tryTrans_ flattenOps ||| tryTrans_ flattenAggr) &&& tryTrans_ mergeSlice )))
    >>> block (tryTrans_ sliceToTuple ||| recurse)

flattenLookupArgs :: Expr -> Maybe Expr
flattenLookupArgs (Lookup sym args) = Just $ Lookup sym (concatMap flattenExprList args)
flattenLookupArgs _ = Nothing

flattenAggr :: AnAggregate -> Maybe AnAggregate
flattenAggr (AggrTuple ls) = Just $ AggrTuple (concatMap flattenTuple ls)
  where
    flattenTuple (AggrTuple ls) = ls
    flattenTuple a = [a]
flattenAggr (BaseAg ScalarFD ls)
  | Just len <- shouldSplit ls
  = Just $ AggrTuple [BaseAg ScalarFD (tryMergeSlice $ Proj i len ls) | i <- [0..len-1]]
flattenAggr _ = Nothing

flattenOps :: Expr -> Maybe Expr
flattenOps (BOp Eql l r)
  | Just len <- shouldSplit l
  = Just $ foldr1 (BOp And) [BOp Eql (tryMergeSlice $ Proj i len l) (tryMergeSlice $ Proj i len r) | i <- [0..len-1]]
flattenOps _ = Nothing
-- | Is this a tuple?
shouldSplit :: Expr -> Maybe Int
shouldSplit (HasEType _ _ ty) = case ty of
  (TupleTyp _ l) -> Just (length l)
  _ -> Nothing
shouldSplit (Tuple _ l) = Just $ length l
shouldSplit (Slice _ t _ _) = Just t
shouldSplit _ = Nothing
tryMergeSlice :: Expr -> Expr
tryMergeSlice a = fromMaybe a (mergeSlice a)
