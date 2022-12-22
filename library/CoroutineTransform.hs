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
import Rewrites (VarGenT, withVarGenT, genVar, maxVar, withVarGenT')
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Control.Applicative ((<|>))
import Data.Foldable (foldl')
import Data.Functor.Identity (Identity (runIdentity))
import Debug.Trace (traceM)



data CTEnv = CTEnv {
    nameGen :: Int,
    locals :: S.Set Var,
    generatedBindings :: M.Map Source Lang,
    generatedRequests :: [(Source, [Local], Source, Maybe AggrOp)],
    lastLabel :: Source,
    firstLabel :: Maybe Source
}
type M = VarGenT (State CTEnv)



doCoroutineTransform :: TopLevel -> TopLevel
doCoroutineTransform tl = tl' { defs = M.union funs $ M.union (M.map ([],) (generatedBindings env')) $ defs tl' }
  where
    ((tl', varGen'), env') = runState (withVarGenT' (maxVar tl) out) env0
    env0 = CTEnv 0 S.empty M.empty [] (root tl) Nothing
    collectFree a = freeVarsQ a S.\\  S.fromList (map unSource $ M.keys $ defs tl)

    out = do
      defs' <- forM (M.toList $ defs tl) $ \(k, (_args, e)) -> do
        modify $ \s -> s { firstLabel = Nothing, lastLabel = k }
        e <- runT (coroutineTransform collectFree) e
        ll <- gets lastLabel
        modify $ \s -> s { generatedBindings = renameEntry ll k (generatedBindings s) }
        fl <- gets firstLabel
        pure (fromMaybe k fl, (_args, e))
      pure $ tl { defs = M.fromList defs' }

    sources = M.fromListWith (<>) [ (funTable, [(source, locals)]) | (funTable, locals, source, _) <- generatedRequests env' ]
    aggregates = M.fromListWith (<>) [ (funTable, [op]) | (funTable, _locals, _source, Just op) <- generatedRequests env' ]
    funs = runIdentity $ withVarGenT varGen' $ fmap (M.fromListWith (error "key collision") . concat) $ traverse (uncurry doFun) $ M.toList $ M.filter (not . null . fst) (defs tl)
    -- !_ = error (show sources)
    doFun k (args, body) = do
       body' <- loadInputs args inputs (mapExpr (\x -> Tuple [Pack args, x]) body)
       let aggs = doAggregates k ops
       traceM (show ops)
       pure $ (k, ([], body')):aggs
      where
        inputs = M.findWithDefault [] k sources
        ops = M.findWithDefault [] k aggregates

mapExpr :: (Expr -> Expr) -> Lang -> Lang
mapExpr f (Return a) = Return $ f a
mapExpr f (Bind a v b) = Bind a v (mapExpr f b)
mapExpr f a = runIdentity $ traverseP (pure . mapExpr f) a

doAggregates :: Source -> [AggrOp] -> [(Source, ([a], Lang))]
doAggregates (Source (Var i s)) aggs = [ (Source $ Var i (s ++ "_" ++ show agg), ([], OpLang $ Group agg (LRef $ Var i s))) | agg <- aggs ]

loadInputs :: [Var] -> [(Source, [Local])] -> Lang -> VarGenT Identity Lang
loadInputs _ [] body = pure body
loadInputs locs inps body = do
   let sources =   foldl1 (\a b -> OpLang (Union a b)) (fmap (LRef . unSource . fst) inps)
   l <- genVar "l"
   pure $ Bind  sources l (OpLang $ Unpack (LRef l) locs body)

renameEntry :: Source -> Source -> M.Map Source Lang -> M.Map Source Lang
renameEntry old new m = case m M.!? old of
    Just v -> M.insert new v (M.delete old m)
    Nothing -> m


tellRequest :: Var -> (Var, Maybe AggrOp, Thunk) -> Lang -> M Lang
tellRequest s (v, op, Thunk sym args) lan = do
    modify $ \env -> env { generatedRequests = (sourceToRequest sym, args, Source s, op) : generatedRequests env }
    pure $ OpLang $ Lookup (Source $ sourceToOp op sym) args v lan

tellRequests :: Var -> [(Var, Maybe AggrOp, Thunk)] -> Lang -> M Lang
tellRequests _ [] lan = pure lan
tellRequests v (x:xs) lan = do
    r <- tellRequests v xs lan
    tellRequest v x r

sourceToOp :: Maybe AggrOp -> Source -> Var
sourceToOp Nothing (Source s) = s
sourceToOp (Just op) (Source (Var i v)) = Var i (v ++ "_" ++ show op)
sourceToRequest :: Source -> Source
sourceToRequest (Source (Var i v)) = Source $ Var i v

coroutineTransform :: (Lang -> S.Set Var) -> Trans M
coroutineTransform freeVars = tryTransM (\rec -> \case
    w@(AsyncBind binds e :: Lang) -> Just $ do
      let frees = freeVars w
      stash <- genVar "stash"
      -- old <- gets label
      -- tempVar <- genVar "temp"
      out <- tellRequests stash binds =<< rec e
      bindVar <- genVar "l"
      outLabel <- genVar "out"
      let nested = Bind (LRef stash) bindVar (OpLang $ Unpack (LRef bindVar) (S.toList frees) out)
      tellGenerated outLabel nested
      modify $ \s -> s { firstLabel = firstLabel s <|> Just (Source stash), lastLabel = Source outLabel }
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

