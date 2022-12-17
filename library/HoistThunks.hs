{-# LANGUAGE LambdaCase #-}
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
gatherThunks = runWriterT . runT (
    tryTransM @Expr (\_rec -> \case
      AThunk t -> Just $ do
        v <- genVar "t"
        tell [(v,Nothing, t)]
        pure (Ref v)
      Aggr op th -> Just $ do
        v <- genVar "t"
        tell  [(v, Just op, th)]
        pure (Ref v)
      _ -> Nothing
    ) ||| recurse
   
  )
