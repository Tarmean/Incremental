{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module HoistThunks where


import CompileQuery
import OpenRec
import Rewrites
import Data.Functor.Identity (Identity (runIdentity))
import Control.Monad.Writer.Strict (WriterT(..), tell)
import Data.Data (Data)
import Control.Monad
import Control.Lens
import Control.Monad.State.Strict
import qualified Data.Map as M

doLifting :: TopLevel -> TopLevel
doLifting a = runIdentity $ withVarGenT (maxVar a) (runT liftThunksT a)

liftThunksT :: Trans (VarGenT Identity)
liftThunksT =
  tryTransM @Lang (\rec -> \case
    Bind a v b -> Just $ do
       (a', binds) <- gatherThunks a
       b' <- rec b
       asyncBind binds (Bind a' v b')
    Return e -> Just $ do
       (a', binds) <- gatherThunks e
       asyncBind binds (Return a')
    _ -> Nothing
  ) ||| recurse

asyncBind :: [(Var, Maybe AggrOp, Source, [Expr])] -> Lang -> VarGenT Identity Lang
asyncBind [] lang = pure lang
asyncBind ls lang = do
    (os, lets) <- flip runStateT mempty $ do
        flip (traverseOf (each . _4 . each)) ls $ \case
           Ref v -> pure v
           i -> do
              o <- genVar "a"
              at o ?= i
              pure o
    let mkLets lang0 = foldr (\(a, b) c -> OpLang (Let a b c)) lang0 (M.toList lets)
    pure (mkLets (AsyncBind [(v,bop,Thunk s args) | (v,bop,s,args) <- os] lang))
gatherThunks :: Data a => a -> VarGenT Identity (a, [(Var, Maybe AggrOp, Source, [Expr])])
gatherThunks = runWriterT . runT
    (   tryTransM_ @Expr \case
            -- AThunk t -> Just $ do
            --   v <- genVar "t"
            --   tell [(v,Nothing, t)]
            --   pure (Ref v)
            Aggr bop (Thunk s args) -> Just $ do
              v <- genVar "t"
              tell  [(v, Just bop, s, map Ref args)]
              pure (Ref v)
            _ -> Nothing
    ||| tryTransM_ @Lang \case
            OpLang (Force (Thunk sym args)) -> Just $ do
              v <- genVar "t"
              tell [(v, Nothing, sym, fmap Ref args)]
              pure (Bind (LRef (unSource sym)) v 
                      (Filter (BOp Eql (Proj 0 2 (Ref v)) (Tuple (fmap Ref args))) (Return (Proj 1 2 (Ref v)))))
            OpLang (Call (HasEType _ e (ListTy (SourceTy sym) (TupleTyp ls)))) -> Just $ do
              v <- genVar "t"
              let tot = length ls
              let args = [Proj i tot e | i <- [0..tot-1]]
              tell [(v, Nothing, sym, args)]
              pure (
                Bind (LRef (unSource sym)) v 
                      (Filter (BOp Eql (Proj 0 2 (Ref v)) (Tuple args)) (Return (Proj 1 2 (Ref v)))))

            _ -> Nothing
    ||| recurse
    )
