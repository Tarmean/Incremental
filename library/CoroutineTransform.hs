{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
-- | work together with HoistThunks to remove nested tables and functions
--
-- This replaces nested calls to some sub-query`l`
-- into a single global query which turns a table filled with all arguments into a table with all results
--
-- (If the function is recursive the query will be recursive, obviously, so this is neater with seminaive evaluation)
--
-- We take an `AsyncBind l b` and splits it by
-- - skipping the rest of the query, only saving locals into a temporary table
-- - Using the temp table, we insert l into a request table 
-- - We generate an extra query which joins the result table for l with the temp table execute b
--
module CoroutineTransform where

import CompileQuery
import OpenRec
import qualified Data.Map as M
import qualified Data.Set as S
import Rewrites (VarGenT, withVarGenT, genVar, maxVar)
import Control.Monad.State
import Control.Monad.Reader
import Debug.Trace (traceM)



data CTEnv = CTEnv {
    nameGen :: Int,
    locals :: S.Set Var,
    generatedBindings :: M.Map Source Lang,
    generatedRequests :: [(Source, [Local], Source, Maybe AggrOp)]
}
type M = ReaderT Source (VarGenT (State CTEnv))


doCoroutineTransform :: TopLevel -> TopLevel
doCoroutineTransform tl = tl' { defs = M.union (M.map ([],) (generatedBindings env')) (defs tl') }
  where
    (tl', env') = runState (withVarGenT (maxVar tl) out) env0
    env0 = CTEnv 0 S.empty M.empty []
    out = do
      defs' <- flip M.traverseWithKey (defs tl) $ \k (_args, e) -> do
        e <- runReaderT (runT coroutineTransform e) k
        pure (_args, e)
      pure $ tl { defs = defs' }


tellRequest :: (Var, Maybe AggrOp, Thunk) -> Lang -> M Lang
tellRequest (v, op, Thunk sym args) lan = do
    s <- genVar "p"
    modify $ \env -> env { generatedRequests = (sourceToRequest sym, args, Source s, op) : generatedRequests env }
    pure $ OpLang $ Lookup (Source $ sourceToOp op sym) args v lan

tellRequests :: [(Var, Maybe AggrOp, Thunk)] -> Lang -> M Lang
tellRequests [] lan = pure lan
tellRequests (x:xs) lan = do
    r <- tellRequests xs lan
    tellRequest x r

sourceToOp :: Maybe AggrOp -> Source -> Var
sourceToOp Nothing (Source s) = s
sourceToOp (Just op) (Source (Var i v)) = Var i (v ++ "_" ++ show op)
sourceToRequest :: Source -> Source
sourceToRequest (Source (Var i v)) = Source $ Var i (v ++ "_request")

coroutineTransform :: Trans M
coroutineTransform = tryTransM (\rec -> \case
    w@(AsyncBind binds e :: Lang) -> Just $ do
      let frees = freeVarsQ w
      root <- ask
      tempVar <- genVar "temp"
      out <- tellRequests binds =<< local (const (Source tempVar)) (rec e)
      bindVar <- genVar "l"
      let nested = Bind (LRef $ unSource root) bindVar (OpLang $ Unpack (LRef bindVar) (S.toList frees) out)
      tellGenerated tempVar nested
      pure (Return (Pack (S.toList frees)))
    _ -> Nothing)
    ||| recurse

tellGenerated :: Var -> Lang -> M ()
tellGenerated v l = modify $ \env -> env { generatedBindings = M.insert (Source v) l (generatedBindings env) }

-- newtype Ctx r m a = { onSuccess :: a -> r }
-- out: Lang -> Lang
-- inner: (a -> m Lang) -> m Lang
--
--
-- pseudocode, for now:

-- handle (Bind a v b) = do
--    a <- handle a
--    Bind a v <$> cut (handle b)
-- handle (AThunk (Thunk f ls)) = do
--     ctx <- getContext
--     locals <- getLocals
--     temp <- Temp ctx (Return (Pack locals))
--     makeRequests f ls temp
--     v1 <- genVar
--     v2 <- genVar
--     let ctx' a = For v1 temp (Unpack ls v1) (Lookup v2 f (Tuple ls) a)
--     setContext ctx'
--     pure (proj "out" v2)



-- Pause a computation, compute a request, and resume with the result.
--
-- This requires four steps:
-- - Store live variables in a temp table
-- - Project the request into a request table
-- - Calculate the result table from the request table
-- - Join the temp table with the result table
--
-- This is Datalog's Magic Set transform, and C#'s coroutine transform
--
-- We need to split a single query into a sequence slices. This will be a traversal with a monad transformer.
--
-- Example:
-- @
-- let v_1 = for l_2 in #user {yield (l_2, SUM(v_5(l_2)))}
--     v_5[l_2] = for l_6 in #foo {when (l_2 == l_6::AnyType) yield l_6}
-- in v_1
-- @
--
-- Here, @SUM(v_5(l_2))@ is a thunk in a strict context.
--
-- @
-- let v_temp_1 = for l_2 in #user {yield pack{l_2}}
--     vreq_5 = v_temp_1
--     vres_5 = groupBy(SUM, for l_2 in vreq_5 { for l_6 in #foo {when (l_2 == l_6::AnyType) yield Tuple [l_2, l_6] }})
--  --    v_5[l_2] = for l_6 in #foo {when (l_2 == l_6::AnyType) yield l_6}
--     v_1 = for l_2 in v_temp_1 { yield (l_2, v_5[l_2]) }
-- in v_1
-- @
--
--Which should simplify to
-- @
-- let vres_5 = groupBy(SUM, for l_2 in #user { for l_6 in #foo {when (l_2 == l_6::AnyType) yield Tuple [l_2, l_2] }})
--     v_1 = for l_2 in #user { yield (l_2, v_5[l_2]) }
-- in v_1
-- @

