{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
-- | Use congruence closure+rewrite rules to reason about SQL queries
module CongruenceClosure where


import Control.Monad.State

import Data.Equality.Graph.Monad

import qualified CompileQuery as Q
import qualified Control.Monad.State as S
import Data.Equality.Analysis (Analysis)
import Data.Equality.Graph (Language, ClassId, ENode(..))
import Data.Ord.Deriving (deriveOrd1)
import Data.Eq.Deriving (deriveEq1)
import Data.Coerce (coerce)
import SQL
import Control.Lens hiding (op)
import Control.Monad.Reader
import Control.Monad.Trans.Elevator
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)


-- [Note: Why E-Graphs]
--
-- Take this query:
--
-- @
-- SELECT U.user_id, J.sum
-- FROM users U
--   INNER JOIN
--     (SELECT J.user_id, SUM(J.cost) as sum FROM jobs J GROUP BY J.user_id) J
--    ON U.user_id = J.user_id
-- @
--
-- Is it equivalent to the following?
-- @
-- SELECT J.user_id, SUM(J.cost) as sum
-- FROM jobs J
-- WHERE J.user_id in (SELECT U.user_id FROM users)
-- GROUP BY J.user_id J
-- @
--
-- Yes, but only if the users table has user_id as primary key. If so, then for
-- each tuple in `jobs` there is only one `user`, so we can shift the join
-- inside the GROUP BY without affecting cardinalities. From there, we can use
-- equality reasoning to replace `U.user_id` with `J.user_id`, at which point
-- we have no reference to `U` and can turn it into an existential join. If
-- there is a foreign key constraint, we can even get rid of the WHERE clause.
--
--
-- But this reasoning is complicated and fraught with peril. The fundep chasing is
-- a hypergraph breadth-first search. The equality reasoning is hash-consing.
-- The foreign key reasoning can be expressed as propagating `not_null(p)` in
-- datalog-like rules. They all have to be interleaved.
--
-- E-Graphs support all of this, so we go with them.

-- [Note: Formalism]
--
-- One approach in the literature focuses on semigroups. Queries are a logic formula which check whether an argument tuple is in the result. 
--
--  So `FROM users U` becomes `exists U. U \in users & ...`. This `U` stands for a specific tuple in the database, not just its values. You can think of it as a memory address, though e.g. join results do not map to static tables.
--
--  We can make existential quantifiers implicit and always pull them to the top-level.
--
--
--  Aggregates do not quite fit this thought process.
--


newtype EggT anl l a = MonadEgg { unMonadEgg :: StateT Int (EGraphM anl l ) a }
    deriving (Functor, Applicative, Monad)

class (Monad m, Analysis anl l, Language l) => MonadEgg anl l m | m -> anl l where
    liftEgg :: EGraphM anl l a -> m a
    genVar :: m ClassId
    genSkolem :: String -> m SkolemIdent
    mergeVars :: ClassId -> ClassId -> m ()

deriving  via Elevator (ReaderT r) m instance MonadEgg anl l m => MonadEgg anl l (ReaderT r m)
instance (MonadTrans t, Monad (t m), MonadEgg anl l m) => MonadEgg anl l (Elevator t m) where
    liftEgg = lift . liftEgg
    genVar = lift genVar
    genSkolem = lift . genSkolem
    mergeVars = (lift .) . mergeVars

data SomeValue a
    = Name Q.Var
    | Proj a SQL.AField
    | SkolemFun SkolemIdent [a]
    | Fun SkolemIdent [a]
    | Joined a a
    | JoinProj1 a
    | JoinProj2 a
    | Try a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable)
type SkolemIdent = String

deriveEq1   ''SomeValue
deriveOrd1  ''SomeValue
instance Language SomeValue where
instance (Analysis l SomeValue) => MonadEgg l SomeValue (EggT l SomeValue) where
    liftEgg = MonadEgg . lift
    genVar = MonadEgg $ do
        i <- S.get
        S.put (i+1)
        lift $ add (coerce (Name (Q.Var i "v") :: SomeValue ClassId))
    genSkolem tag = MonadEgg $ do
        i <- S.get
        S.put (i+1)
        pure (tag <> show i)
    mergeVars l r = liftEgg (void $ merge l r)

addTerm :: (MonadEgg l SomeValue m) => SomeValue ClassId -> m ClassId
addTerm = liftEgg . add . coerce

alignFields :: (Monad m, Foldable t, MonadEgg anl SomeValue m) => t AField -> ClassId -> ClassId -> m ()
alignFields fields l r = 
  forM_ fields $ \field -> do
      lf <- addTerm (Proj l field)
      rf <- addTerm (Proj r field)
      mergeVars lf rf

runToGraph :: SQL -> (([AField], ClassId), EGraph () SomeValue)
runToGraph sql = egraph $ evalStateT (unMonadEgg (runReaderT (makeGraph sql) mempty)) 0

mkFun :: (MonadEgg l SomeValue m) => String -> [ClassId] -> m ClassId
mkFun tag args = addTerm (Fun tag args)
mkSkolemFun :: (MonadEgg l SomeValue m) => String -> [ClassId] -> m ClassId
mkSkolemFun tag args = do
    sk <- genSkolem tag
    addTerm (SkolemFun sk args)
makeGraph :: (MonadReader (M.Map Q.Var ClassId) m, MonadEgg l SomeValue m) => SQL -> m ([AField], ClassId)
makeGraph (OrderBy _ spj) = makeGraph spj
makeGraph (GroupQ groupBys spj) = do
   groupBysI <- traverse mkExpr groupBys
   out <- mkSkolemFun "group_fundep" groupBysI
   (fields, inner) <- makeGraph spj
   alignFields fields out inner
   pure (fields, out)
makeGraph (Table meta name) = do
    out <- addTerm (SkolemFun name [])
    forM_ (coerce (Q.fundeps meta) :: [[String]]) $ \fd -> do
       args <- traverse addTerm (Proj out <$> fd)
       fun <- mkSkolemFun ("fd_" <> name) args
       mergeVars out fun
    pure (Q.fields meta, out)
makeGraph (Slice _ _ spj) = makeGraph spj
makeGraph (DistinctQ spj) = do
   (fields, inner) <- makeGraph spj
   innerFields <- traverse addTerm (Proj inner <$> fields)
   out <- mkSkolemFun "distinct" innerFields
   alignFields fields out inner
   pure (fields, out)
makeGraph (ASPJ (SPJ {sources, wheres, proj})) = do
    outs <- traverseOf (each . _2) makeGraph sources
    let bindings = M.fromList [(name, out) | (name, (_, out)) <- outs]
    joinResult <- mkSkolemFun "join" (M.elems bindings)
    local (M.union bindings) $ do
        wheresI <- traverse mkWhere wheres
        projI <- traverse (mkExprQ joinResult) proj
        forM_ (M.toList projI) $ \(name, out) -> do
            t <- addTerm (Proj out name)
            mergeVars out t
        out <- mkFilter (catMaybes wheresI) joinResult
        pure (M.keys proj, out)

mkFilter :: MonadEgg l SomeValue m => [ClassId] -> ClassId -> m ClassId
mkFilter [] p = pure p 
mkFilter _ _ = error "Todo: Add non-equijoins"
    
mkExprQ :: (MonadEgg l SomeValue m, MonadReader (M.Map Q.Var ClassId) m) => ClassId -> Expr -> m ClassId
mkExprQ ctx (AggrOp op _) = mkSkolemFun (show op) [ctx]
mkExprQ _ a = mkExpr a

mkExpr :: (MonadEgg l SomeValue m, MonadReader (M.Map Q.Var ClassId) m) => Expr -> m ClassId
mkExpr (Singular q) = snd <$> makeGraph q
mkExpr (Lit l) = mkFun (show l) []
mkExpr (BOp op l r) = do
   l' <- mkExpr l
   r' <- mkExpr r
   mkFun (show op) [l', r']
mkExpr (Ref v proj) = do
   asks (M.lookup v) >>= \case
       Nothing -> error $ "Unknown variable: " <> show v
       Just x -> addTerm (Proj x proj)
mkExpr (AggrOp op _) = error $ "AggrOp not allowed here: " <> show op


-- TODO: Track whether this is a non-null context before doing this transformation
mkWhere :: (MonadEgg l SomeValue m, MonadReader (M.Map Q.Var ClassId) m) => Expr -> m (Maybe ClassId)
mkWhere (BOp Q.Eql l r) = do
    li <- mkExpr l
    ri <- mkExpr r
    mergeVars li ri
    pure Nothing
mkWhere o = do
    o' <- mkExpr o
    pure (Just o')

-- deriveEq1   ''SymExpr
-- deriveOrd1  ''SymExpr

-- data PatEnv lang = PatEnv { uniqSupply :: Int, matchLang :: M.Map (lang Var) Var }
-- type M lang =  State (PatEnv lang)

-- toQuery :: (Traversable l, Ord (l Var)) => Pattern l -> M l Var
-- toQuery (VariablePattern v) = pure v
-- toQuery (NonVariablePattern l) = traverse toQuery l >>= resolveMatch

-- compileToQuery :: (Traversable l, Ord (l Var)) => Pattern l -> (Var, M.Map (l ClassIdOrVar) ClassIdOrVar)
-- compileToQuery p = (pOut, outMap)
--   where
--     (pOut, envOut) = runState (toQuery p) (PatEnv (maxVar p+1) mempty)
--     outMap = M.mapKeysMonotonic (fmap CVar) $ M.map CVar $ matchLang envOut

-- -- | Generate a fresh variable
-- nextVar :: M l Var
-- nextVar = do
--    i <- gets uniqSupply
--    modify $ \s -> s { uniqSupply = uniqSupply s + 1}
--    pure i

-- -- | HashCons for variable patterns
-- resolveMatch :: (Ord (l Var)) => l Var -> M l Var
-- resolveMatch matcher =
--     gets (M.lookup matcher . matchLang) >>= \case
--         Just existingName -> pure existingName
--         Nothing -> do
--            newName <- nextVar
--            modify $ \s -> s { matchLang = M.insert matcher newName (matchLang s) }
--            pure newName


-- maxVar :: Foldable l => Pattern l -> Var
-- maxVar l = maximum (0:vars l)
--   where
--     vars (VariablePattern v) = [v]
--     vars (NonVariablePattern l') = concatMap vars l'

