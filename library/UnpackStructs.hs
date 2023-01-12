{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- | Map nested structs to flat tuples, and projections to flat slices
module UnpackStructs where


import CompileQuery
import OpenRec
import qualified Data.Map.Strict as M
import Data.Data (Data)


-- | Calculate how many columns a type consumes
widthOfType :: (Source -> Int) -> ExprType -> Int
widthOfType _ (EBase _) = 1
widthOfType env (TupleTyp ls) = sum (map (widthOfType env) ls)
widthOfType argCount (ListTy source _) = case source of
   SourceTy s -> argCount s
   RootTy -> 0
   _ -> error "Invalid listTy"
widthOfType _ e = error ("wrong kind in widthOfType: " <> prettyS e)

projToSlice :: (Source -> Int) -> Expr -> Maybe Expr
projToSlice _ (Proj 0 1 e) = Just $ e
projToSlice env (Proj field _total (HasEType _ expr (TupleTyp tys))) = Just $ Slice offset width expr
  where
    (l,x) = case splitAt field tys of
        (l, x:_) -> (l,x)
        _ -> undefined
    offset = sum (map (widthOfType env) l)
    width = widthOfType env x
projToSlice _ _ = Nothing


unpackStructs :: TopLevel -> TopLevel
unpackStructs tl = runT' (tryTrans_ (projToSlice env) ||| recurse) tl
  where
    env x = length $ fst $ defs tl M.! x

mergeSlice :: Expr -> Maybe Expr
mergeSlice (Slice i _ (Slice k l e)) = Just $ Slice (i+k) l e
mergeSlice _ = Nothing

mergeSlices :: Data a => a -> a
mergeSlices = runT' (recurse >>> tryTrans_ mergeSlice)
