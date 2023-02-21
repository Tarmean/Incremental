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
widthOfType env (TupleTyp ls) = sum (map (widthOfType env) ls)
widthOfType argCount (ListTy source _) = case source of
   SourceTy s -> argCount s
   RootTy -> 0
   _ -> error "Invalid listTy"
widthOfType _ e = error ("wrong kind in widthOfType: " <> prettyS e)

flattenType :: [ExprType] -> [ExprType]
flattenType ls = concatMap go ls
  where
    go (TupleTyp ls) = concatMap go ls
    go a = [a]

projToSlice :: (Source -> Int) -> Expr -> Maybe Expr
-- projToSlice _ (Proj 0 1 e) = Just $ e
projToSlice env (Proj field _total (HasEType _ expr (TupleTyp tys)))
  | resultIsTuple = Just $ Slice offset width (length (flattenType tys)) expr
  where
    (l,x) = case splitAt field tys of
        (l, x:_) -> (l,x)
        _ -> undefined
    offset = sum (map (widthOfType env) l)
    width = widthOfType env x
    resultIsTuple = case tys !! field of
      TupleTyp {} -> True
      _ -> False
projToSlice _ _ = Nothing


unpackStructs :: TopLevel -> TopLevel
unpackStructs tl = runT' (tryTrans_ (projToSlice env) ||| recurse) tl
  where
    env x = length $ fst $ defs tl M.! x

mergeSlice :: Expr -> Maybe Expr
mergeSlice (Slice i _ total (Slice k l _ e)) = Just $ Slice (i+k) l total e
mergeSlice (Slice i _ total (Proj k _ e)) = Just $ Proj (i+k) total e
mergeSlice (Proj i _ (Slice off _ total e)) = Just $ Proj (i+off) total e
mergeSlice _ = Nothing

sliceToTuple :: Lang -> Maybe Lang
sliceToTuple (Return (Slice k l t e)) = Just $ Return (Tuple [Proj (k+i) t e | i <- [0..l-1]])
sliceToTuple _ = Nothing

flattenTuple :: Expr -> Maybe Expr
flattenTuple (Tuple ls)
  | any isTuple ls = Just $ Tuple (concatMap flattenExprList ls)
  where
    isTuple (Tuple {}) = True
    isTuple (Slice {}) = True
    isTuple _ = False
flattenTuple _ = Nothing
flattenExprList :: Expr -> [Expr]
flattenExprList = go
  where
    go (Tuple ls) = concatMap go ls
    go (Slice from to total ls) = [Proj i total ls | i <- [from..from+to-1]]
    go a = [a]

refToSlice  :: Expr -> Maybe Expr
refToSlice (HasEType _ (Ref r) (TupleTyp tys)) = Just $ Slice 0 width width (Ref r)
  where
    width = sum (map (widthOfType (const 0)) tys)
refToSlice _ = Nothing

dropTyp  :: Expr -> Maybe Expr
dropTyp (HasEType _ r _) = Just r
dropTyp _ = Nothing

mergeSlices :: Data a => a -> a
mergeSlices = runT' $ do
    block (recurse >>> (tryTrans_ refToSlice ||| tryTrans_ dropTyp ||| (tryTrans_ updateGroup &&& tryTrans_ flattenTuple &&& tryTrans_ flattenLookupArgs &&& tryTrans_ flattenOps &&& tryTrans_ mergeSlice )))
    >>> block (tryTrans_ sliceToTuple ||| recurse)

updateGroup :: OpLang -> Maybe OpLang
updateGroup (Group l _ k (OpLang (HasType _ e (ListTy _ (TupleTyp ls))))) = Just (Group widthL widthR k e)
  where
    (tyL, tyR) = splitAt l ls
    widthL = sum (map (widthOfType (const 0)) tyL)
    widthR = sum (map (widthOfType (const 0)) tyR)
updateGroup _ = Nothing

flattenLookupArgs :: Expr -> Maybe Expr
flattenLookupArgs (Lookup sym args) = Just $ Lookup sym (concatMap flattenExprList args)
flattenLookupArgs _ = Nothing

flattenOps :: Expr -> Maybe Expr
flattenOps (BOp Eql l r)
  | Just len <- shouldSplit l
  = Just $ Tuple [BOp Eql (tryMergeSlice $ Proj i len l) (tryMergeSlice $ Proj i len r) | i <- [0..len-1]]
  where
    tryMergeSlice a = fromMaybe a (mergeSlice a)
    shouldSplit (HasEType _ _ ty) = case ty of
      (TupleTyp l) -> Just (length l)
      _ -> Nothing
    shouldSplit (Tuple l) = Just $ length l
    shouldSplit (Slice _ t _ _) = Just t
    shouldSplit _ = Nothing
flattenOps _ = Nothing
