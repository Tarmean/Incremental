{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
module HoistThunks where


import CompileQuery
import OpenRec
import Rewrites
import Data.Functor.Identity (Identity (runIdentity))
import Control.Monad.Writer.Strict (WriterT(..), tell)
import Data.Data (Data)

doLifting :: TopLevel -> TopLevel
doLifting a = runIdentity $ withVarGenT (maxVar a) (runT liftThunksT a)

liftThunksT :: Trans (VarGenT Identity)
liftThunksT =
  tryTransM @Lang (\rec -> \case
    Bind a v b -> Just $ do
       (a', binds) <- gatherThunks a
       b' <- rec b
       pure $ asyncBind binds (Bind a' v b')
    Return e -> Just $ do
       (a', binds) <- gatherThunks e
       pure $ asyncBind binds (Return a')
    _ -> Nothing
  ) ||| recurse

asyncBind :: [(Var, Maybe AggrOp, Thunk)] -> Lang' t -> Lang' t
asyncBind [] a = a
asyncBind binds a = AsyncBind binds a
gatherThunks :: Data a => a -> VarGenT Identity (a, [(Var, Maybe AggrOp, Thunk)])
gatherThunks = runWriterT . runT
    (   tryTransM_ @Expr \case
            -- AThunk t -> Just $ do
            --   v <- genVar "t"
            --   tell [(v,Nothing, t)]
            --   pure (Ref v)
            Aggr op th -> Just $ do
              v <- genVar "t"
              tell  [(v, Just op, th)]
              pure (Ref v)
            _ -> Nothing
    ||| tryTransM_ @Lang \case
            OpLang (Force t@(Thunk sym args)) -> Just $ do
              v <- genVar "t"
              tell [(v, Nothing, t)]
              pure (Bind (LRef (unSource sym)) v 
                      (Filter (BOp Eql (Proj 0 2 (Ref v)) (Tuple args)) (Return (Proj 1 2 (Ref v)))))
            OpLang (Call (HasEType _ e (ThunkTy [sym] (ListTy (TupleTyp ls))))) -> Just $ do
              v <- genVar "t"
              let tot = length ls
              let args = [Proj i tot e | i <- [0..tot-1]]
              let thunk = Thunk (Source $ unFun sym) args
              tell [(v, Nothing, thunk)]
              pure (
                Bind (LRef (unFun sym)) v 
                      (Filter (BOp Eql (Proj 0 2 (Ref v)) (Tuple args)) (Return (Proj 1 2 (Ref v)))))

            _ -> Nothing
    ||| recurse
    )
