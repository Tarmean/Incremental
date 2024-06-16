{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveAnyClass #-}
-- | Synatx tree types, pretty printing, and core Definitions
module CompileQuery (module CompileQuery, module Util) where
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad.State
import Control.Monad
import Data.Data
import qualified Data.Map.Lazy as LM
import Data.Reify
import GHC.IO (unsafePerformIO)
import Prettyprinter
import GHC.Stack.Types (HasCallStack)
import GHC.Generics (Generic)
import OpenRec
import Data.List (intersperse)
import Util
import Data.Hashable (Hashable(..))
import Data.Maybe (catMaybes)
import Data.Functor.Identity (runIdentity)
import qualified Data.ByteString.Char8 as BS
import Data.Hashable (Hashable)

-- Plan for aggregates:
--
-- Do a Fold operation+monoid decorators. Tuples of monoids form a monoid. Aggregates like sum or window functions are monoids.
--
-- But we extend SQL:
--
-- - Singleton maps are built like `key := someMonoidValue` and form monoids
-- - list(expr) and set(expr) are monoids which stand for collections
--
-- We do not get flat values for everything.
-- The solution is that Folds of tuples are tuples of Folds. We
--
-- - For each key prefix we generate a Fold
-- - for collection aggregates we define a thunk+toplevel function
--
-- [keys := list(s)]_env => Thunk(new_thunk, [])
--    def new_thunk(): for ps in env: yield [keys, s]
--
-- Map results are just tables with extra columns for the keys. We support
--
-- - indexing
-- - toList
--
-- toList forces the thunk.
-- indexing is a lookup op, but what if the result is another collection? Then we generate a new thunk with a function which forces+filters the indexed thunk.
-- This requires type information, though


-- | AST's are tagged by a `phase` parameter.
-- - If phase is 'Nest, the types are not inspectable.
-- - If phase is 'Flat, all functions are replaced by explicit binders.
--
-- TraverseP is a traversal which changes this parameter.
-- The monad `m` handles name generation and observable sharing.
--
-- Only `Lang' p` is a GADT which uses the parameter, which makes the mutually recursive
class TraverseP f where
   traverseP :: (HasCallStack, Applicative m) => (Lang' p -> m (Lang' 'Flat)) -> f p -> m (f 'Flat)


-- [Note: Observable sharing]
-- Haskell allows for recursive definitions
--
--
-- > f = do
-- >    x <- ([1,2,3] <> f)
-- >    pure (x*2)
--
-- This is cute, but not observable. An AST defined this way 
-- uses finite memory, but causes infinite loops when forced.
--
-- Observable sharing replaces pointers with inspectable variables
--
-- > ("f", Bind (Union (Lit [1,2,3]) (Var "f")) "x" (BinOp Mul (Var "x") (Lit 2)))
-- GHC offers a mechanism for (mostly) stable pointer names called StableNames.
-- The data-reify library uses it to turn recursive definitions into inspectable AST's.
-- We will use a fork of the data-reify library which is much nicer with
-- mutually recursive types.

-- | A thunk is a delayed function call, represented by it's captured
-- environment.
-- > f(1,2,3)
-- >
-- > struct F_thunk(Int,Int,Int);
-- > force(F_thunk(1,2,3)) = f(1,2,3)
--
-- We can represent nested containers as the free variables needed to generate them.
-- Only when we consume the container do we need to evaluate the thunk, which (mostly) absolves us from ever representing nested data.
--
-- Of course sharing could get lost if we just re-compute this data, so as a seconds tep we do memoization using a coroutine transformation.
data Thunk = Thunk { atSource :: Source, atArgs :: [Var] }
  deriving (Eq, Ord, Show, Data)

(</>) :: Doc s -> Doc s -> Doc s
a </> b = a <> line <> b

instance Pretty Thunk where
    pretty (Thunk s as) = pretty s <> tupled (map pretty as)


data ConstrTag = ConstrTag { conName :: BS.ByteString, conArity :: Int }
  deriving (Eq, Ord, Show, Data)

tuple :: [Expr' r] -> Expr' r
tuple ls = Tuple (tupleTag (length ls)) ls
tupleTyp :: [ExprType] -> ExprType
tupleTyp ls = TupleTyp (tupleTag (length ls)) ls
tupleTag :: Int -> ConstrTag
tupleTag = ConstrTag "Tuple"
isTupleTag :: ConstrTag -> Bool
isTupleTag (ConstrTag "Tuple" _) = True
isTupleTag _ = False


instance Pretty ConstrTag where
    pretty c
      | isTupleTag c = ""
      | otherwise = pretty (BS.unpack $ conName c)

-- | AST for Expression language
data Expr' (p::Phase) where
    Ref :: Var -> Expr' p
    AThunk :: Thunk -> Expr' p
    Proj :: Int -> Int -> (Expr' p) -> Expr' p
    Slice :: Int -> Int -> Int -> (Expr' p) -> Expr' p
    BOp :: BOp -> Expr' p -> Expr' p -> Expr' p
    Unit :: Expr' p
    Tuple :: ConstrTag -> [Expr' p] -> Expr' p
    Aggr :: AggrOp -> Thunk -> Expr' p
    AggrNested :: AggrOp -> (Lang' p) -> Expr' p
    Nest :: Lang' a -> Expr' a
    Lookup :: { lookupTable :: Source, lookupKeys :: [Expr' p] } -> Expr' p
    Singular :: Lang' p -> Expr' p
    HasEType :: TypeStrictness -> Expr' p -> ExprType -> Expr' p
    Lit :: ALit -> Expr' p
deriving instance Eq Expr
deriving instance Ord Expr
deriving instance Show Expr
deriving instance Data Expr


-- | Base aggregates enriched
data AnAggregate' (p :: Phase)
    = BaseAg AggrOp (Expr' p) -- ^ Base aggregate, e.g. SUM(cost)
    | MapOf (Expr' p) (AnAggregate' p) -- ^ Grouping aggregate, (M.singleton k v). Merging a map merges the matching keys
    | AggrTuple [AnAggregate' p] -- ^ A tuple-aggregate produces a tuple of aggregates 
    | ListOf (Expr' p) -- ^ Not an aggregate as such, produces in a table reference
    | SetOf (Expr' p) -- ^ ListOf with @distinct@ on top
    -- | WindowFun  -- | Todo
instance TraverseP AnAggregate' where
    traverseP f (BaseAg op e) = BaseAg op <$> traverseP f e
    traverseP f (MapOf e ag) = MapOf <$> traverseP f e <*> traverseP f ag
    traverseP f (AggrTuple ags) = AggrTuple <$> traverse (traverseP f) ags
    traverseP f (ListOf e) = ListOf <$> traverseP f e
    traverseP f (SetOf e) = SetOf <$> traverseP f e
instance Pretty AnAggregate where
    pretty (BaseAg op e) = pretty op <> parens (pretty e)
    pretty (MapOf e ag) = pretty e <> " := " <> pretty ag
    pretty (AggrTuple ags) = tupled $ map pretty ags
    pretty (ListOf e) = "list" <> parens (pretty e)
    pretty (SetOf e) = "set" <> parens (pretty e)
deriving instance Eq AnAggregate
deriving instance Ord AnAggregate
deriving instance Show AnAggregate
deriving instance Data AnAggregate
type AnAggregate = AnAggregate' 'Flat
-- | An aggregate may contain multiple incompatible group-bys which SQL doesn't support.
-- We partition the sub-expressions by key context.
--
-- >  fold [p] projects (p.category := (list(p.name), p.sub_category := sums(p.cost))) :: DSL (Map String ([String], Map String Int))
--
-- context of list(p.name): @KeyContext (fromList [k1]) False@
-- translation: @SELECT p.category, p.name FROM projects@
--
-- context of sums(p.cost): @KeyContext (fromList [k1,k2]) True@
-- translation: @SELECT p.category, p.sub_category, SUM(p.cost) FROM projects GROUP BY p.category,p.sub_category@
data KeyContext' p = KeyContext { outerKeys :: S.Set (Expr' p), flatGroup :: Bool }
type KeyContext = KeyContext' 'Flat

deriving instance Eq KeyContext
deriving instance Ord KeyContext
deriving instance Show KeyContext
deriving instance Data KeyContext
instance Pretty KeyContext where
    pretty (KeyContext ks isFlat)
      | S.null ks = mempty
      | isFlat = "group-by " <> tupled (map pretty $ S.toList ks)
      | otherwise = "with segments " <> tupled (map pretty $ S.toList ks)


instance TraverseP KeyContext' where
    traverseP f (KeyContext ks b) = KeyContext <$> fmap S.fromList (traverse (traverseP f) $ S.toList ks) <*> pure b


-- [Note: Map Operations]
-- A @DSL (Map k v)@ is represented as a table @DSL [(k,v)]@. We support two main operations:
--
-- - toList (it's just a typecast)
-- - Indexing
--
--
-- Indexing is a bit harder because we need two implementation strategies:
--
-- - If the result is a scalar, we can do a lookup. This compiles to a scalar query in SQL
--
-- @
-- {someMap !? k}
--
-- (SELECT m.rhs
-- FROM [someMap] m
-- WHERE m.lhs = [k])
-- @
--
--
-- But what if the map holds nested containers? Easy, project them:
--
-- @
-- {fold [p] projects (p.category := (list(p.name), p.sub_category := sums(p.cost))) :: DSL (Map String ([String], Map String Int))}
--
--
-- def cat_nested():
--    for p in projects:
--       yield ((p.category,),p.name)
--
-- def cat_subcat_flat():
--    fold [p] projects (p.category, (p.subCategory, (sum(p.name)))):
--
-- def proj_cat(k):
--    for (cat, name) in cat_nested:
--       if cat == k:
--         yield name
--
-- def proj_cat_subcat_flat1(k):
--    for (cat, o) in cat_subcat_flat():
--       if cat == k:
--         yield o
--
-- def proj_cat_subcat_flat2(k,k2):
--    for (subcatcat, o) in proj_cat_subcat_flat1(k):
--       if subcat == o:
--         yield o
--
-- {proj ! k}
-- (Thunk(proj_cat, k), Thunk(proj_cat_subcat_flat(k)))
-- @
--
-- Can we unify these helper functions? Well, maybe:
--
-- @
-- def Project<K extends Eq, V, T extends [(K,V)]>(m: T, k: K) -> [V]:
--     for (a,b) in force_thunk(m):
--       if a == k:
--         yield b
-- @
--
-- But we do need a monomorphised copy for the thunk-forcing coroutine transformation. 

data ALit = IntLit Int | StrLit String
  deriving (Eq, Ord, Show, Data)
instance Pretty ALit where
   pretty (IntLit i) = pretty i
   pretty (StrLit i) = pretty (show i)


instance TraverseP Expr'  where
   traverseP _ (Ref a) = pure (Ref a)
   traverseP _ (AThunk a) = pure $ AThunk a
   traverseP f (Proj i tot e) = Proj i tot <$> traverseP f e
   traverseP f (Slice l r tot e) = Slice l r tot <$> traverseP f e
   traverseP f (BOp op a b) = BOp op <$> traverseP f a <*> traverseP f b
   traverseP _ Unit = pure Unit
   traverseP f (Tuple ct es) = Tuple ct <$> traverse (traverseP f) es
   traverseP f (AggrNested op a) = AggrNested op <$> f a
   traverseP _ (Aggr _ _) = error "aggr"
   traverseP f (Nest o) = Nest <$> f o
   traverseP f (HasEType r ex t) = HasEType r <$> traverseP f ex <*> pure t
   traverseP f (Lookup sym es) = Lookup sym <$> traverse (traverseP f) es
   traverseP f (Singular e) = Singular <$> f e
   traverseP _ (Lit i) = pure (Lit i)
(.==) :: Expr' p -> Expr' p -> Expr' p
(.==) = BOp Eql
data AggrOp = SumT | MinT | MaxT
            | ScalarFD -- ^ Imagine we group by user_id and want to select username
                       -- The username is uniquely determined by the id, so the
                       -- standard says we can select it as a scalar. 
                       -- Some DBs (cough oracle cough) don't implement this correctly
  deriving (Eq, Ord, Show, Data)
type Expr = Expr' 'Flat
data ExprType = TupleTyp ConstrTag [ExprType] | ListTy ExprType ExprType | UnificationVar Int | SourceTy Source | RootTy | LocalTy | EBase TypeRep  | TypeError ExprType ExprType
  deriving (Eq, Ord, Show, Typeable)
intTy :: ExprType
intTy = EBase (typeRep (Proxy :: Proxy Int))
stringTy :: ExprType
stringTy = EBase (typeRep (Proxy :: Proxy String))
boolTy :: ExprType
boolTy = EBase (typeRep (Proxy :: Proxy Bool))

instance Data ExprType where
    gfoldl _ z a@EBase {} = z a
    gfoldl k z (TupleTyp ct ls)       = z TupleTyp `k` ct `k` ls
    gfoldl k z (ListTy t v) = z ListTy `k` t `k` v
    gfoldl k z (UnificationVar v) = z UnificationVar `k` v
    gfoldl k z (SourceTy v) = z SourceTy `k` v
    gfoldl _ z RootTy = z RootTy
    gfoldl _ z LocalTy = z LocalTy
    gfoldl k z (TypeError a b) = z TypeError `k` a `k` b

    gunfold k z c
      = case constrIndex c of
        7 -> k (k (z TypeError))
        6 -> z LocalTy
        5 -> z RootTy
        4 -> k (z SourceTy)
        3 -> k (z UnificationVar)
        2 -> k (k (z ListTy))
        1 -> k (k (z TupleTyp))
        i -> error ("illegal constructor index in expr" <> show i)

    toConstr EBase {} = eBaseConstr
    toConstr ListTy {} = eListTypeConstr
    toConstr TupleTyp {} = eTupleConstr
    toConstr UnificationVar {} = eUnificationVarConstr
    toConstr SourceTy {} = eSourceTyConstr
    toConstr RootTy {} = eRootTyConstr
    toConstr LocalTy {} = eLocalTyConstr
    toConstr TypeError {} = eTypeError

    dataTypeOf _ = exprTypeDataType

eSourceTyConstr :: Constr
eBaseConstr, eListTypeConstr, eTupleConstr, eRootTyConstr, eLocalTyConstr, eUnificationVarConstr, eTypeError :: Constr
eBaseConstr = mkConstr exprTypeDataType "EBase" [] Prefix
eListTypeConstr = mkConstr exprTypeDataType "AnyType" [] Prefix
eUnificationVarConstr = mkConstr exprTypeDataType "UnificationVar" [] Prefix
eTupleConstr = mkConstr exprTypeDataType "Tuple" [] Prefix
eSourceTyConstr = mkConstr exprTypeDataType "SourceTy" [] Prefix
eRootTyConstr = mkConstr exprTypeDataType "RootTy" [] Prefix
eLocalTyConstr = mkConstr exprTypeDataType "LocalTy" [] Prefix
eTypeError = mkConstr exprTypeDataType "TypeError" [] Prefix
exprTypeDataType :: DataType
exprTypeDataType = mkDataType "ExprType" [eTupleConstr, eListTypeConstr, eUnificationVarConstr, eSourceTyConstr, eRootTyConstr, eLocalTyConstr, eTypeError]

newtype Uniq = Uniq Int
  deriving (Eq, Show, Ord, Data)
data BOp = Eql | Mult | And
  deriving (Eq, Ord, Show, Data)
data Phase = Rec | Flat
data Lang' (t::Phase) where
  Bind :: { boundExpr ::  Lang' t, boundVar :: Var, boundBody :: Lang' t } -> Lang' t
  Filter :: Expr' t -> Lang' t -> Lang' t
  Return :: (Expr' t) -> Lang' t
  OpLang :: OpLang' t -> Lang' t
  LRef :: Var -> Lang' t
  AsyncBind :: [(Var, Maybe AggrOp, Thunk)] -> Lang' t -> Lang' t
  FBind :: Lang' 'Rec -> (Expr' 'Rec -> Lang' 'Rec) -> Lang' 'Rec
deriving instance Eq Lang
deriving instance Ord Lang
deriving instance Show Lang
instance Data Lang where
    gfoldl :: (forall d b. Data d => c (d -> b) -> d -> c b) -> (forall g. g -> c g) -> Lang -> c Lang
    gfoldl k z (Bind a b c) = z Bind `k` a `k` b `k` c
    gfoldl k z (Filter a b) = z Filter `k` a `k` b
    gfoldl k z (Return a) = z Return `k` a
    gfoldl k z (OpLang a) = z OpLang `k` a
    gfoldl k z (LRef a) = z LRef `k` a
    gfoldl k z (AsyncBind ls a) = z AsyncBind `k` ls `k` a
    gunfold k z c
      = case constrIndex c of
        1 -> k (k (k (z Bind)))
        2 -> k (k (z Filter))
        3 -> k (z Return)
        4 -> k (z OpLang)
        5 -> k (z LRef)
        6 -> k (k (z AsyncBind))
        i -> error ("illegal constructor index in lang" <> show i)
    toConstr (Bind {}) = bindConstr
    toConstr (Filter {}) = filterConstr
    toConstr (Return {}) = returnConstr
    toConstr (OpLang {}) = opLangConstr
    toConstr (LRef {}) = lRefConstr
    toConstr (AsyncBind {}) = asyncBindConstr
    dataTypeOf _ = langDataType
bindConstr, filterConstr, returnConstr, opLangConstr, lRefConstr, fBindConstr,asyncBindConstr :: Constr
bindConstr = mkConstr langDataType "Bind" [] Prefix
filterConstr = mkConstr langDataType "Filter" [] Prefix
returnConstr = mkConstr langDataType "Return" [] Prefix
opLangConstr = mkConstr langDataType "OpLang" [] Prefix
lRefConstr = mkConstr langDataType "LRef" [] Prefix
fBindConstr = mkConstr langDataType "FBind" [] Prefix
asyncBindConstr = mkConstr langDataType "AsyncBind" [] Prefix
langDataType :: DataType
langDataType = mkDataType "Lang" [bindConstr, filterConstr, returnConstr, opLangConstr, lRefConstr, asyncBindConstr]




instance TraverseP Lang' where
    traverseP f (Bind l v l') = Bind <$> f l <*> pure  v <*> f l'
    traverseP f (Filter e l) = Filter <$> traverseP f e <*> f l
    traverseP f (Return e) = Return <$> traverseP f e
    traverseP f (OpLang op) = OpLang <$> traverseP f op
    traverseP _ (LRef v) = pure (LRef v)
    traverseP f (AsyncBind ls l) = AsyncBind ls <$> f l
    traverseP _ (FBind _ _) = undefined -- FBind <$> (traverseP f l) <*> (traverseP f . g)
data TypeStrictness = Inferred | Given
  deriving (Eq, Ord, Show, Data)

data TableMeta = TableMeta { fundeps :: FunDeps, fields :: [String] }
  deriving (Show, Eq, Ord, Data, Generic)
newtype FunDeps = FD [[String]]
  deriving (Show, Eq, Ord, Data, Generic)
data OpLang' (t::Phase)
  = Opaque String TableMeta
  | Union (Lang' t) (Lang' t)
  | Unpack { unpack :: Expr' t, labels :: [Maybe Var], unpackBody :: Lang' t }
  | Let { letVar :: Var, letExpr :: Expr' t, letBody :: Lang' t }
  | Fold { foldVar :: Var, context :: KeyContext' t, foldResult :: AnAggregate' t, foldSource :: Lang' t }
  | Call { nestedCall :: Expr' t }
  | Distinct (Lang' t)
  | Force { thunked :: Thunk }
  | HasType { rigidity :: TypeStrictness, langType :: Lang' t, hasTypeType :: ExprType }
type OpLang = OpLang' 'Flat
deriving instance Eq OpLang
deriving instance Ord OpLang
deriving instance Show OpLang
deriving instance Data OpLang
instance TraverseP OpLang' where
    traverseP _ (Opaque s m) = pure $ Opaque s m
    traverseP f (Union l l') = Union <$> traverseP f l <*> traverseP f l'
    traverseP f (Unpack a b c) = Unpack <$> traverseP f a <*> pure b <*> f c
    traverseP f (Let v e b) = Let v <$> traverseP f e <*> f b
    traverseP f (Fold bound ctx res agg) = Fold bound <$> traverseP f ctx <*> traverseP f res <*> f agg
    traverseP f (HasType r a b) = HasType r <$> f a <*> pure b
    traverseP f (Call b) = Call <$> traverseP f b
    traverseP f (Distinct b) = Distinct <$> f b
    traverseP _ (Force b) = pure $ Force b
type Lang = Lang' 'Flat
type RecLang = Lang' 'Rec
newtype Source = Source { unSource :: Var}
  deriving (Eq, Ord, Show, Data)
data Var = Var { uniq :: Int, name :: String }
  deriving stock (Eq, Ord, Show, Data, Generic)
instance Hashable Var where
  hashWithSalt salt (Var uq _) = hashWithSalt salt uq
  
newtype Fun = Fun { unFun :: Var}
  deriving (Eq, Ord, Show, Data)
type Local = Var
data TopLevel' p = TopLevel {
  defs :: M.Map Source ([Local], p),
  root :: Source
}
  deriving (Eq, Ord, Show, Data)

-- Fixme: Currently the precedence is sort of broken, we elide parens but sometimes they are necessary.
-- There are two classic approaches:
-- - Order the prettyprinter recursion to mirror a recursive LL parser.
--   We have one function which matches * and /, and on failure we dispatch to the +- function. At the bottom we add a parens and start back at the top.
--   Problem: If we miss a case we cycle.
-- - Add an integer arg to the prettyprinter which is the precedence of the parent. If the precedence of the current node is lower, we add parens.
--   This is what ReadS does and it works well, but is annoying to manage manually.
--   Maybe do a ReaderT wrapper around Doc, and implement the (<>) operator as `liftA2 (<>)`?
--   Should we track left/right associativity?
--

instance Pretty Var where
   pretty (Var v n) = pretty n <> "_" <> pretty v
instance Pretty Fun where
   pretty (Fun f) = pretty f
instance Pretty Source where
    pretty (Source s) = pretty s
instance Pretty ExprType where
    pretty (EBase t) = pretty (show t)
    pretty (TupleTyp ct [a]) = pretty ct <> "(" <> pretty a <> ",)"
    pretty (TupleTyp ct ts) = pretty ct <> tupled (map pretty ts)
    pretty (ListTy RootTy l) = brackets (pretty l)
    pretty (ListTy t l) = brackets (pretty l) <> "@" <> pretty t
    pretty (SourceTy o) = pretty o
    pretty (UnificationVar uv) = "UV<" <> pretty uv <> ">"
    pretty RootTy = "RootTy"
    pretty (TypeError a b) = "TypeError<" <> pretty a <> "," <> pretty b <> ">"
    pretty LocalTy = "<HigherOrder>"
instance Pretty BOp where
    pretty Eql = "=="
    pretty And = "&&"
    pretty Mult = "*"
instance Pretty AggrOp where
    pretty SumT = "SUM"
    pretty MinT = "MIN"
    pretty MaxT = "MAX"
    pretty ScalarFD = "UNIQUE"
instance Pretty Expr where
    pretty (Ref t) = pretty t
    pretty (Proj i _tot e) = pretty e <> "." <> pretty i
    pretty (Slice l r _total e) = pretty e <> "[" <> pretty l <> ":" <> pretty l<> "+" <>pretty r <> "]"
    pretty (BOp op e1 e2) = pretty e1 <+> pretty op <+> pretty e2
    pretty Unit = "()"
    pretty (Aggr op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (AggrNested op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (Tuple ct [a]) = pretty ct <> "(" <> pretty a <> ",)"
    pretty (Tuple ct es) = pretty ct <> tupled (map pretty es)
    pretty (AThunk a) = pretty a
    pretty (Nest a) = "Nest" <+> pretty a
    pretty (HasEType Inferred e ty) = parens $ pretty e <+> ":::" <+> pretty ty
    pretty (HasEType _ e ty) = pretty e <+> "::" <+> pretty ty
    pretty (Lookup v e) = pretty v <> pretty e
    pretty (Lit i) = pretty i
    pretty (Singular e) = parens (pretty e)
instance Pretty Lang where
    pretty (Bind a b c) = nest 6 $ group $ "for" <+> pretty b <+> "in" <+> optParens (align (pretty a)) <+> "{" <> (line <> pretty c) </> "}"
      where
        optParens d = group $ flatAlt ("("<> line) space <> align d <> flatAlt (line <> ")") space
    pretty (LRef v) = "*" <> pretty v
    pretty (Filter p c) = "when" <+> parens (pretty p) <+> pretty c
    pretty (AsyncBind lets bod) = group $ ("async" <+> align (startEndSep open close sep [maybe "" (\x -> pretty x <> " ") op <> pretty k <+> "=" <+> pretty v | (k,op, v) <- lets])) </> pretty bod
      where
        open = flatAlt "{ " "{ "
        close = flatAlt "}" "}"
        sep = flatAlt "; " "; "
        startEndSep a b c ls =  group $ a <> hcat (intersperse (line' <> c) ls) </> b
    pretty (Return e) = "yield" <+> pretty e
    pretty (OpLang o) = pretty o
instance Pretty OpLang where
    pretty (Opaque s _) = "#" <> pretty s
    pretty (Union a b) = "Union" <+> group (align (pretty a </> pretty b))
    pretty (Unpack a v c) = group $ "let"<+> align (align (mkTuple (map (maybe "_" pretty) v)) <> softline <> "=" <+> pretty a) </> "in" <+> pretty c
      where
       mkTuple [] = "()"
       mkTuple [a] = "(" <> a <> ",)"
       mkTuple as = tupled as
    pretty (Let v e b) = "let" <+> pretty v <+> ":=" <+> pretty e <> flatAlt line " in " <> pretty b
    pretty (Fold bound groupBy res body)
        = group $ hang 2 $
            group ("fold" </> parens (pretty bound <> " in " <> pretty body) </> pretty groupBy) </> pretty res
    pretty (HasType Inferred e t) = parens $ pretty e <+> ":::" <+> pretty t
    pretty (HasType _ e t) = pretty e <+> "::" <+> pretty t
    pretty (Call e) = "?" <> pretty e
    pretty (Force t) = "!" <> pretty t
    pretty (Distinct t) = "Distinct" <+> pretty t
instance Pretty a => Pretty (TopLevel' a) where
    pretty (TopLevel ds root) = nest 2 $ "let" </> vsep (prettyAssignments ds) </> "in " </> pretty root
      where

        prettyAssignments m = [pretty k <> prettyVars vars <+> group (nest 4 ("=" </>  pretty v)) | (k, (vars,v)) <- M.toList m]
        prettyVars [] = mempty
        prettyVars vs = list (map pretty vs)


-- FIXME: shouldn't abstract over toplevel vars into account.
instance (Monad m) => MonadGlobals RecLang (StateT (TopLevel' Lang) m)  where
  tellGlobal k v = modify' $ \tl -> tl { defs = M.insert (Source k) ([], v) (defs tl) }

export :: (MonadGlobals RecLang m, MonadRef m) => Lang ->  m Var
export val = do
    key <- stableName val
    let name = Var key "v"
    doOnce key (tellGlobal @RecLang name val)
    pure name

-- labelFor :: FreeVars (Lang' p) => Lang' p -> String
-- labelFor (OpLang (Opaque s)) = s  <> "s"
-- labelFor c@Comprehend {} 
--   | freeVars c /= S.empty = "f"
-- labelFor _ = "v"
doOnce :: MonadRef m => Unique -> m () -> m ()
doOnce key m = do
    seen <- wasVisited key
    unless seen $ do
      markVisited key
      m

normalize :: forall m. (MonadGlobals RecLang m, MonadRef m) => RecLang -> m Var
normalize (LRef v) = pure v
-- normalize (Return (Ref o)) = normalize o
normalize w@(FBind a f) = do
  key <- stableName w
  let var = Var key "v"
  doOnce key $ do
    l <- freshName
    let local = Var l "l"
    head <- normalize a
    body <- normalize (f (Ref local))
    tellGlobal @RecLang var (Bind (LRef head) local (LRef body))
  pure var
normalize w = do
  key <- stableName w
  let var = Var key "v"
  doOnce key (tellGlobal @RecLang var =<< traverseP (fmap LRef . normalize) w)
  pure var
instance (MonadRef m, MonadGlobals RecLang m) => MuRef RecLang m where
    type DeRef RecLang = Lang
    type Key RecLang = Var
    makeKey _ i = Var i "v"
    mapDeRef _ _ = undefined -- traverse normalize
toTopLevel :: RecLang -> TopLevel' Lang
toTopLevel l = unsafePerformIO $ do
   (var, tl) <- runStable $ runStateT (normalize l) (TopLevel M.empty (Source $ Var 0 "<unknown_root>"))
   pure tl { root = Source var }

type TopLevel = TopLevel' Lang

data TypeEnv = TE { tableTys :: LM.Map Var ExprType, funTys :: LM.Map Fun ExprType }
  deriving (Eq, Ord, Show, Data)
type ScopeEnv = M.Map Var ExprType

withBoundT :: Monad m => (forall a. S.Set Var -> m a -> m a) -> Trans m
withBoundT locally =
     tryTransM @Lang (\rec -> \case
       AsyncBind bound body -> Just (AsyncBind <$> rec bound <*> locally (boundVars bound) (rec body))
       Bind {boundVar, boundExpr, boundBody} -> Just (Bind <$> rec boundExpr <*> pure boundVar <*> locally (S.singleton boundVar) (rec boundBody))
       _ -> Nothing)
 ||| tryTransM @OpLang (\rec -> \case
       (Unpack exp vs body) -> Just (Unpack <$> rec exp <*> pure vs <*> locally (S.fromList $ catMaybes vs) (rec body))
       (Let v exp body) -> Just (Let v <$> rec exp <*> locally (S.singleton v) (rec body))
       _ -> Nothing)
 where boundVars bound = S.fromList [v|(v,_,_) <-  bound]

freeVarsQ :: Data a => a -> S.Set Var
freeVarsQ = runQ ( 
    tryQuery_ @Expr @_  \case
       Ref v ->   Just (S.singleton v)
       _ -> Nothing
 ||| tryQuery @Lang (\rec -> \case
       AsyncBind bound body -> Just (rec bound <> (rec body S.\\ boundVars bound))
       LRef v -> Just (S.singleton v)
       Bind {boundVar, boundExpr, boundBody} -> Just (rec boundExpr <> S.delete boundVar (rec boundBody))
       _ -> Nothing)
 ||| tryQuery @OpLang (\rec -> \case
       (Unpack exp v body) -> Just (rec exp <> (rec body S.\\ S.fromList (catMaybes v)))
       Let var exp body -> Just (rec exp <> S.delete var (rec body))
       _ -> Nothing)
 ||| tryQuery_ @Thunk (\(Thunk (Source v) ls) -> Just (S.insert v (S.fromList ls)))
 ||| recurse)
 where
   boundVars bound = S.fromList [v|(v,_,_) <-  bound]



mapExpr :: (Expr -> Expr) -> Lang -> Lang
mapExpr f = mapExpr' (Return . f)

mapExpr' :: (Expr -> Lang) -> Lang -> Lang
mapExpr' f (Return a) = f a
mapExpr' f (Bind a v b) = Bind a v (mapExpr' f b)
mapExpr' f a = runIdentity $ traverseP (pure . mapExpr' f) a
