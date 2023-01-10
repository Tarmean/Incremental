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
-- | Synatx tree types, pretty printing, and core Definitions
module CompileQuery where
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad.State
import Data.Data
import qualified Data.Map.Lazy as LM
import Data.Reify
import GHC.IO (unsafePerformIO)
import Prettyprinter
import Prettyprinter.Render.String (renderString)
import GHC.Stack.Types (HasCallStack)
import OpenRec
import Data.List (intersperse)
import Data.Maybe (catMaybes)



-- | AST's are tagged by a `phase` parameter.
-- - If phase is 'Nest, the types are not inspectable.
-- - If phase is 'Flat, all functions are replaced by explicit binders.
--
-- TraverseP is a traversal which changes this parameter.
-- The monad `m` handles name generation and observable sharing.
--
-- Only `Lang' p` is a GADT which uses the parameter, which makes the mutually recursive
class TraverseP f where
   traverseP :: (HasCallStack, Applicative m) => (Lang' p -> m (Lang' q)) -> f p -> m (f q)


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

-- | AST for Expression language
data Expr' (p::Phase) where
    Ref :: Var -> Expr' p
    AThunk :: Thunk -> Expr' p
    Proj :: Int -> Int -> (Expr' p) -> Expr' p
    BOp :: BOp -> Expr' p -> Expr' p -> Expr' p
    Unit :: Expr' p
    Tuple :: [Expr' p] -> Expr' p
    Aggr :: AggrOp -> Thunk -> Expr' p
    AggrNested :: AggrOp -> (Lang' p) -> Expr' p
    Nest :: Lang' a -> Expr' a
    Pack :: {  packLabels :: [Var] } ->  Expr' p
    Lookup :: { lookupTable :: Source, lookupKeys :: [Expr] } -> Expr' p
    HasEType :: TypeStrictness -> Expr' p -> ExprType -> Expr' p
deriving instance Eq Expr
deriving instance Ord Expr
deriving instance Show Expr
deriving instance Data Expr


instance TraverseP Expr'  where
   traverseP _ (Ref a) = pure (Ref a)
   traverseP _ (AThunk a) = pure $ AThunk a
   traverseP f (Proj i tot e) = Proj i tot <$> traverseP f e
   traverseP f (BOp op a b) = BOp op <$> traverseP f a <*> traverseP f b
   traverseP _ Unit = pure Unit
   traverseP f (Tuple es) = Tuple <$> traverse (traverseP f) es
   traverseP f (AggrNested op a) = AggrNested op <$> f a
   traverseP _ (Aggr _ _) = error "aggr"
   traverseP f (Nest o) = Nest <$> f o
   traverseP _ (Pack ls) = pure $ Pack ls
   traverseP f (HasEType r ex t) = HasEType r <$> traverseP f ex <*> pure t
   traverseP _ (Lookup sym es) = pure $ Lookup sym es
   -- traverseP f (Unpack e ls b) = Unpack <$> traverseP f e <*> pure ls <*> traverseP f b
(.==) :: Expr' p -> Expr' p -> Expr' p
(.==) = BOp Eql
data AggrOp = SumT | MinT | MaxT
  deriving (Eq, Ord, Show, Data)
type Expr = Expr' 'Flat
data ExprType = TupleTyp [ExprType] | ListTy ExprType ExprType | UnificationVar Int | SourceTy Source | RootTy | LocalTy | EBase TypeRep
  deriving (Eq, Ord, Show, Typeable)
intTy :: ExprType
intTy = EBase (typeRep (Proxy :: Proxy Int))

instance Data ExprType where
    gfoldl _ z a@EBase {} = z a
    gfoldl k z (TupleTyp ls)       = z TupleTyp `k` ls
    gfoldl k z (ListTy t v) = z ListTy `k` t `k` v
    gfoldl k z (UnificationVar v) = z UnificationVar `k` v
    gfoldl k z (SourceTy v) = z SourceTy `k` v
    gfoldl _ z RootTy = z RootTy
    gfoldl _ z LocalTy = z LocalTy

    gunfold k z c
      = case constrIndex c of
        6 -> z LocalTy
        5 -> z RootTy
        4 -> k (z SourceTy)
        3 -> k (z UnificationVar)
        2 -> k (k (z ListTy))
        1 -> k (z TupleTyp)
        i -> error ("illegal constructor index in expr" <> show i)

    toConstr EBase {} = eBaseConstr
    toConstr ListTy {} = eListTypeConstr
    toConstr TupleTyp {} = eTupleConstr
    toConstr UnificationVar {} = eUnificationVarConstr
    toConstr SourceTy {} = eSourceTyConstr
    toConstr RootTy {} = eRootTyConstr
    toConstr LocalTy {} = eLocalTyConstr

    dataTypeOf _ = exprTypeDataType

eSourceTyConstr :: Constr
eBaseConstr, eListTypeConstr, eTupleConstr, eRootTyConstr, eLocalTyConstr, eUnificationVarConstr :: Constr
eBaseConstr = mkConstr exprTypeDataType "EBase" [] Prefix
eListTypeConstr = mkConstr exprTypeDataType "AnyType" [] Prefix
eUnificationVarConstr = mkConstr exprTypeDataType "UnificationVar" [] Prefix
eTupleConstr = mkConstr exprTypeDataType "Tuple" [] Prefix
eSourceTyConstr = mkConstr exprTypeDataType "SourceTy" [] Prefix
eRootTyConstr = mkConstr exprTypeDataType "RootTy" [] Prefix
eLocalTyConstr = mkConstr exprTypeDataType "LocalTy" [] Prefix
exprTypeDataType :: DataType
exprTypeDataType = mkDataType "ExprType" [eTupleConstr, eListTypeConstr, eUnificationVarConstr, eSourceTyConstr, eRootTyConstr, eLocalTyConstr]

newtype Uniq = Uniq Int
  deriving (Eq, Show, Ord, Data)
data BOp = Eql
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
data OpLang' (t::Phase)
  = Opaque String
  | Union (Lang' t) (Lang' t)
  | Unpack { unpack :: Lang' t, labels :: [Maybe Var], unpackBody :: Lang' t }
  | Let { letVar :: Var, letExpr :: Expr' t, letBody :: Lang' t }
  | Group { groupBy :: AggrOp, groupBody :: Lang' t }
  | Call { nestedCall :: Expr' t }
  | Force { thunked :: Thunk }
  | HasType { rigidity :: TypeStrictness, langType :: Lang' t, hasTypeType :: ExprType }
  | Distinct (Lang' t)
type OpLang = OpLang' 'Flat
deriving instance Eq OpLang
deriving instance Ord OpLang
deriving instance Show OpLang
deriving instance Data OpLang
instance TraverseP OpLang' where
    traverseP _ (Opaque s) = pure $ Opaque s
    traverseP f (Union l l') = Union <$> traverseP f l <*> traverseP f l'
    traverseP f (Unpack a b c) = Unpack <$> f a <*> pure b <*> f c
    traverseP f (Let v e b) = Let v <$> traverseP f e <*> f b
    traverseP f (Group a c) = Group a <$> f c
    traverseP f (HasType r a b) = HasType r <$> f a <*> pure b
    traverseP f (Call b) = Call <$> traverseP f b
    traverseP f (Distinct b) = Distinct <$> traverseP f b
    traverseP _ (Force b) = pure $ Force b
type Lang = Lang' 'Flat
type RecLang = Lang' 'Rec
newtype Source = Source { unSource :: Var}
  deriving (Eq, Ord, Show, Data)
data Var = Var { uniq :: Int, name :: String }
  deriving (Eq, Ord, Show, Data)
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
    pretty (TupleTyp [a]) = "(" <> pretty a <> ",)"
    pretty (TupleTyp ts) = parens (hsep (punctuate comma (map pretty ts)))
    pretty (ListTy RootTy l) = brackets (pretty l)
    pretty (ListTy t l) = brackets (pretty l) <> "@" <> pretty t
    pretty (SourceTy o) = pretty o
    pretty (UnificationVar uv) = "UV<" <> pretty uv <> ">"
    pretty RootTy = "RootTy"
    pretty LocalTy = "<HigherOrder>"
instance Pretty BOp where
    pretty Eql = "=="
instance Pretty AggrOp where
    pretty SumT = "SUM"
    pretty MinT = "MIN"
    pretty MaxT = "MAX"
instance Pretty Expr where
    pretty (Ref t) = pretty t
    pretty (Proj i _ e) = pretty e <> "." <> pretty i
    pretty (BOp op e1 e2) = pretty e1 <+> pretty op <+> pretty e2
    pretty Unit = "()"
    pretty (Aggr op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (AggrNested op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (Tuple [a]) = "(" <> pretty a <> ",)"
    pretty (Tuple es) = tupled (map pretty es)
    pretty (AThunk a) = pretty a
    pretty (Nest a) = "Nest" <+> pretty a
    pretty (Pack a) = tupled (map pretty a)
    pretty (HasEType Inferred e ty) = parens $ pretty e <+> ":::" <+> pretty ty
    pretty (HasEType _ e ty) = pretty e <+> "::" <+> pretty ty
    pretty (Lookup v e) = pretty v <+> brackets (pretty e)
instance Pretty Lang where
    pretty (Bind a b c) = group $ nest 2 $ "for" <+> pretty b <+> "in" <+> align (pretty a) <+> "{" <> nest 2 (line <> pretty c) </> "}"
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
    pretty (Opaque s) = "#" <> pretty s
    pretty (Union a b) = "Union" <+> group (align (pretty a </> pretty b))
    pretty (Unpack a v c) = group $ "let"<+> align (align (tupled (map (maybe "_" pretty) v)) <> softline <> "=" <+> pretty a) </> "in" <+> pretty c
    pretty (Let v e b) = "let" <+> pretty v <+> ":=" <+> pretty e <> flatAlt line " in " <> pretty b
    pretty (Group op body) = group $ "group" <> parens (pretty op) <+> pretty body
    pretty (HasType Inferred e t) = parens $ pretty e <+> ":::" <+> pretty t
    pretty (HasType _ e t) = pretty e <+> "::" <+> pretty t
    pretty (Call e) = "?" <> pretty e
    pretty (Force t) = "!" <> pretty t
    pretty (Distinct t) = "Distinct" <+> pretty t
instance Pretty a => Pretty (TopLevel' a) where
    pretty (TopLevel ds root) = "let " <> align (vsep (prettyAssignments ds)) </> "in " </> pretty root
      where

        prettyAssignments m = [pretty k <> prettyVars vars <+> "=" <+>  pretty v | (k, (vars,v)) <- M.toList m]
        prettyVars [] = mempty
        prettyVars vs = list (map pretty vs)

prettyS :: Pretty a => a -> String
prettyS = renderString . layoutPretty defaultLayoutOptions . pretty

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . prettyS

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
