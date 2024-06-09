{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Use newtype instead of data" #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MonoLocalBinds #-}
-- | Use congruence closure+rewrite rules to reason about SQL queries
module CongruenceClosure where


import Control.Monad.State

import Data.Equality.Graph.Monad hiding (gets)

import Control.Monad.Trans.Maybe (MaybeT(..))
import qualified CompileQuery as Q
import qualified Control.Monad.State as S
import Data.Hashable (Hashable)
import Data.Equality.Compiler.API as API
import Data.Equality.Analysis (Analysis)
import Data.Equality.Graph (Language, ClassId, ENode(..))
import qualified Data.Equality.Graph.Lens as Gl
import Data.Equality.Compiler.API
import Data.Equality.Matching.Pattern (pat)
import Data.Ord.Deriving (deriveOrd1)
import Data.Eq.Deriving (deriveEq1)
import Data.Coerce (coerce)
import SQL
import Control.Lens hiding (op, (.=))
import Control.Monad.Reader
import Control.Monad.Trans.Elevator
import qualified Data.Map.Strict as M
import Data.Maybe (catMaybes)
import InlinePrettyEGraph -- Data.Equality.Graph.Dot
import Prettyprinter
import Data.Functor.Classes
import Util(prettyS)
import RenderHypergraph (renderGv)
import Unsafe.Coerce (unsafeCoerce)
import Control.Monad
<<<<<<< HEAD
import Data.Hashable (Hashable)
=======
>>>>>>> 951dff022790d2f9e4cefe7e08b642ccb3c48649
import GHC.Generics (Generic)

-- thoughtsf.
-- select * from
-- users u left outer join
-- (select * from jobs j natural join project n where j.type = Good) j
-- where u.id = j.user_id

-- u(uid, uname) in users
-- nn(u)

-- j(jid, userid, jobtype, projectid) in jobs
-- p(projectid) in projects

-- #nt
-- jobtype != good -> #nt = false
-- #nt = true -> jobtype = good
-- #nt = true -> nn(j)
-- #nt = true -> nn(p)
-- nn(j) -> #nt
-- n(j) -> !#nt
-- #nt -> nn(j)
-- !#nt -> n(j)

-- #ot -> nn(u)

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
    deriving newtype (Functor, Applicative, Monad)

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

type FDIdent = String

-- | Sql queries as predicate calculus. The query is a boolean predicate like
-- forall x = (a,b,c), y = (a,h). InTable(x, Users) & InTable(y, Jobs) & b > 2
data EGLang a
<<<<<<< HEAD
    = LTuple { tupleId :: a, tupleVals :: a} -- tuple is a list of columns plus a synthetic tid. Intuitively tid is the memory location so we can reason about duplicates/updating/etc. There is always a function lookup_tuple_xyz(tid) equivalent to the tuple
    -- | LFun String [a] -- function, e.g. a primary key is a function from id column to the tuple
    | InTable a String -- predicates, is tuple in table
    | IsNull a -- for notnull, a tuple can be null - this just sets all values null
    | IsFound a
    | TupleProj a Int
    | FunDep FDIdent [a]
=======
    = LTuple { tupleId :: a, tupleVals :: [a]} -- tuple is a list of columns plus a synthetic tid. Intuitively tid is the memory location so we can reason about duplicates/updating/etc. There is always a function lookup_tuple_xyz(tid) equivalent to the tuple
    | LFun String [a] -- function, e.g. a primary key is a function from id column to the tuple
    | InTable a a -- predicates, is tuple in table
    | IsNull a -- for notnull, a tuple can be null - this just sets all values null
    | IsFound a
    | BaseTable String
>>>>>>> 951dff022790d2f9e4cefe7e08b642ccb3c48649
    | AOp COp a a -- bin ops
    | CTrue
    | CFalse
    | CNot a -- negation
<<<<<<< HEAD
    | LSelectProjectJoin { boundVars :: a, predicate :: a }
    | LList [a] 
    -- | LAggregate {
    --    boundVars :: [a],
    --    selectAggKey :: [a],
    --    selectAggValue,
    --    predicate :: a
    --} -- | Groupby is like a select project join, but the select
    --                        --is split into two pieces. The key uniquely determines the tuple, as usual.
    --                        --The value is the aggregate result for the key. 
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Hashable)

-- addProjections _ = forEachMatch ["r" .= pat (LTuple "xs" "ys")] $ \subst -> do
--     l <- subst "r"
--     ns <- gets (^. Gl._class l . Gl._nodes) 
--     forM_ ns $ \n -> case n of
--         Node (LList ms) -> do
--             forM_ (zip [0..] ms) $ \(i, m) -> do
--               o <- subst (pat (TupleProj m i))
--               merge l o
--         _ -> pure ()

data COp = CEq | CAnd | COr | CLT | CLTE
    deriving (Eq, Ord, Show, Generic, Hashable)


=======
    -- | a :=> a -- implication for proofs
    | LSelectProjectJoin { producedTuple :: a, predicate :: a }
    | LAggregate {
        boundVars :: [a],
        selectAggKey :: [a],
        selectAggValue,
        predicate :: a
    } -- | Groupby is like a select project join, but the select
                            --is split into two pieces. The key uniquely determines the tuple, as usual.
                            --The value is the aggregate result for the key. 
    deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable)
    deriving (Generic)

data Mult = Zero | One | Many
  deriving (Eq, Ord, Show, Enum, Bounded)
data Range a = Range { low :: a, high:: a}
  deriving (Eq, Ord, Show)

union :: Ord a => Range a -> Range a -> Range a
union (Range l r)(Range x y) = Range (min l x) (max r y)
intersect :: Ord a => Range a -> Range a -> Range a
intersect (Range l r)(Range x y) = Range (max l x) (min r y)

mult :: Mult -> Mult -> Mult
mult Zero _ = Zero
mult _ Zero = Zero
mult One One = One
mult _ _ = Many
appRange :: (t1 -> t2 -> a) -> Range t1 -> Range t2 -> Range a
appRange f (Range l r) (Range x y) = Range (f l x) (f r y)

multRange :: Range Mult -> Range Mult -> Range Mult
multRange = appRange mult
addRange :: Range Mult -> Range Mult -> Range Mult
addRange = appRange max

isBoolean :: EGLang a -> Bool
isBoolean (IsNull {}) = True
isBoolean (IsFound {}) = True
isBoolean (AOp {}) = True
isBoolean (CTrue {}) = True
isBoolean (CFalse {}) = True
isBoolean (CNot {}) = True
isBoolean _ = False
ana :: EGLang (Range Mult) -> Range Mult
ana CTrue = Range One One
ana CFalse = Range Zero Zero
ana b | isBoolean b = Range Zero One
ana (LFun _ ls) = Range (minimum (fmap low ls)) (maximum (fmap high ls))
ana (InTable _ a) = a
ana _ = Range Zero Many




rules :: API.Rule f m
rules = undefined
deriving anyclass instance Hashable a => Hashable (EGLang a)
data COp = CEq | CAnd | COr | CLT | CLTE
    deriving (Eq, Ord, Show ,Generic, Hashable)
>>>>>>> 951dff022790d2f9e4cefe7e08b642ccb3c48649

data SomeValue a
    = Name Q.Var
    | Proj a SQL.AField
    | SkolemFun SkolemIdent [a]
    | Fun String [a]
    -- | Joined a a
    | JoinProj Q.Var a
    -- | JoinProj2 a
<<<<<<< HEAD
    -- | Try a 
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Generic, Hashable)
=======
    -- | Try a
    deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Hashable, Generic)
>>>>>>> 951dff022790d2f9e4cefe7e08b642ccb3c48649
data SkolemIdent = SkolemID { skolName :: String, skolUniq :: Int }
    deriving (Eq, Ord, Show, Generic, Hashable)

instance Pretty a => Pretty (SomeValue a) where
   pretty (Name v) = pretty v
   pretty (Proj a f) = pretty a <> "." <> pretty f
   pretty (SkolemFun s as) = "?" <> pretty (skolName s) <> tupled (map pretty as)
   pretty (Fun s as) = pretty s <> tupled (map pretty as)
   pretty (JoinProj v a) = pretty a <> ".sources" <> brackets (pretty v)


data PrettyDict a
    = PrettyDict
    { prettyImpl :: forall dec. a -> Doc dec
    , prettyListImpl :: forall dec. [a] -> Doc dec
    }

data Box a = Box a
data Dict p where
   Dict :: p => Dict p

instance Show1 SomeValue where
   liftShowsPrec showI showL _prec val = withPretty (toPrettyDict showI showL) (prettyS val <>)
   liftShowList showI showL val = withPretty (toPrettyDict showI showL) (prettyS val <>)

toPrettyDict ::  (Int -> a -> ShowS) -> ([a] -> ShowS) -> PrettyDict a
toPrettyDict show1 showsList = PrettyDict
    { prettyImpl = \a -> pretty (show1 0 a "")
    , prettyListImpl = \x -> pretty (showsList x "")
    }

{-# NOINLINE withPretty #-}
prettyToDict :: PrettyDict a -> Dict (Pretty a)
prettyToDict dict = unsafeCoerce (Box dict)

tryM :: Monad m => MaybeT m a -> m ()
tryM m = do
  _ <- runMaybeT m
  pure ()

withPretty :: forall a r. PrettyDict a -> (Pretty a => r) -> r
withPretty dict f = case prettyToDict dict of
    Dict -> f

deriveEq1   ''SomeValue
deriveOrd1  ''SomeValue
instance (Analysis l SomeValue) => MonadEgg l SomeValue (EggT l SomeValue) where
    liftEgg = MonadEgg . lift
    genVar = MonadEgg $ do
        i <- S.get
        S.put (i+1)
        lift $ add (coerce (Name (Q.Var i "v") :: SomeValue ClassId))
    genSkolem tag = MonadEgg $ do
        i <- S.get
        S.put (i+1)
        pure (SkolemID tag i)
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
runToGraph sql = egraph $ flip evalStateT 0 $ unMonadEgg $ flip runReaderT mempty  $ do
    (fields, cid)<- makeGraph sql
    root <- addTerm (Name (Q.Var 0 "root"))
    liftEgg $ do
        _ <- merge root cid
        rebuild
    pure (fields, cid)


dumpGraph :: FilePath -> SQL -> IO ()
dumpGraph path sql = do
    let ((_fields, _root), graph) = runToGraph sql
    renderGv path (toDotGraph graph)
    -- putStrLn $ "Fields: " <> show fields
    -- putStrLn $ "Root: " <> show root
    -- putStrLn $ "Graph: " <> show graph

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
   (fields, inner) <- makeGraph spj
   out <- mkFun "group" (inner:groupBysI)
   forM_ groupBysI $ \gk -> do
      key <- mkSkolemFun "group_key" [out]
      mergeVars gk key
   alignFields fields out inner
   pure (fields, out)
makeGraph (Table meta name) = do
    out <- mkSkolemFun name []
    forM_ (coerce (Q.fundeps meta) :: [[String]]) $ \fd -> do
       args <- traverse (addTerm . Proj out) fd
       fun <- mkFun ("fd_" <> name) args
       mergeVars out fun
    pure (Q.fields meta, out)
makeGraph (Slice _ _ spj) = makeGraph spj
makeGraph (DistinctQ spj) = do
   (fields, inner) <- makeGraph spj
   innerFields <- traverse (addTerm . Proj inner) fields
   out <- mkSkolemFun "distinct" innerFields
   alignFields fields out inner
   pure (fields, out)
makeGraph (ASPJ (SPJ {sources, wheres, proj})) = do
    outs <- forM sources $ \(k,v) -> do
        (fields, out) <- makeGraph v
        name <- addTerm (Name k)
        mergeVars name out
        pure (k, (fields, out))
    let bindings = M.fromList [(name, out) | (name, (_, out)) <- outs]
    joinResult <- mkSkolemFun "join" (M.elems bindings)
    forM_ (M.toList bindings) $ \(k,cid) -> do
        isProjSource <- mkSkolemFun (prettyS k) [joinResult]
        mergeVars cid isProjSource
    local (M.union bindings) $ do
        wheresI <- traverse mkWhere wheres
        forM_ (M.toList proj) $ \(k,v) -> do
            outExpr <- mkExprQ joinResult v
            t <- addTerm (Proj joinResult k)
            mergeVars outExpr t
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
   -- asks (M.lookup v) >>= \case
       -- Nothing -> do
          x <- addTerm (Name v)
          addTerm (Proj x proj)
       -- Just x -> addTerm (Proj x proj)
mkExpr (AggrOp Q.ScalarFD e) = mkExpr e
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

