{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase #-}
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


-- let v_1 = for l_2 in v_3
--            yield (l_2, SUM(v_4(l_2)))
--     v_3 = OpLang Opaque user
--     v_4[l_2] = for l_5 in v_6
--                where [l_2 == l_5::AnyType]
--                 yield l_5
--     v_6 = OpLang Opaque foo
-- in v_1


-- let vt1_2 = for l_2 in v_3
--                yield (old.l_2, v_4_sum[old.l_2]))
--     v_3 = OpLang Opaque user

--     v_4_sum = groupBy(sum, v4_resp)
--     v4_resp = for l_5 in v_6, l_2 in v_3
--                where [l_2 == l_5::AnyType]
--                 yield l_5
--     v_6 = OpLang Opaque foo
-- in v_1

-- Idea: Flatten chains of binds into a flat n-ary join
--     Bind m 'x' (Bind n 'y' Filter (Proj 0 'x' = Proj 1 'y') (Return e))
-- to
--     Comprehend [('x', m), ('y', n)] [Proj 0 'x' = Proj 1 'y'] [] e
--
-- Compile 
--
--     Comprehend ls g p (Op op (Comprehend ...))
-- to
--
--     let F = \fvs -> Comprehend ...
--
-- which magic-tables to 
--
--   F_Requests += fvs
--
--   ... 
-- F_Results = fvs <- F_Requests
--     Comprehend rs ...

-- Comprehend (F_Results, ls) (fvs=fvs':g) p (Op op F_Out)
--
--
--
--
-- Finally, specialize functions
--
--
--
-- SUM(F(x)) => SUM_F(x)
--
-- SUM_F = \fvs -> SUM(...)


-- Could use the GHC rapier for capture avoiding substitutions?

class TraverseP f where
   traverseP :: (HasCallStack, Applicative m) => (Lang' p -> m (Lang' q)) -> f p -> m (f q)
data SomeArg' p = ValArg (Expr' p) | ThunkArg Source ExprType [Expr' p]
deriving instance Eq SomeArg 
deriving instance Ord SomeArg 
deriving instance Show SomeArg 
deriving instance Data SomeArg 
deriving instance Typeable p => Typeable (SomeArg' p) 
instance TraverseP SomeArg'  where
   traverseP f (ValArg e) = ValArg <$> traverseP f e
   -- traverseP f (CollArg l) = CollArg <$> traverseP f l
   traverseP f (ThunkArg s t es) = ThunkArg s t <$> traverse (traverseP f) es

   -- foldP f (ValArg e) = foldP f e
type SomeArg = SomeArg' 'Flat
-- data Typed Var = Typed Var { tvVar :: Var, tvType :: ExprType }
--   deriving (Eq, Ord, Show, Data)
data Typed a = Typed { tyData :: a, tyType :: ExprType }
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
data Thunk = Thunk { atSource :: Source, atArgs :: [Var] }
  deriving (Eq, Ord, Show, Data)
instance Pretty Thunk where
    pretty (Thunk s as) = pretty s <> tupled (map pretty as)
--   ThunkNest :: { atSource :: Source, atArgs :: [SomeArg] } -> Thunked Nest
--   deriving (Eq, Ord, Show, Data)

-- FIXME: Ref and LRef are sort of interchangeable while higher order relations exist.
data Expr' (p::Phase) where
    Ref :: Var -> Expr' p
    AThunk :: Thunk -> Expr' p
    Proj :: ExprType -> Int -> (Expr' p) -> Expr' p
    BOp :: ExprType -> BOp -> (SomeArg' p) -> (SomeArg' p) -> Expr' p
    Unit :: Expr' p
    Tuple :: [Expr' p] -> Expr' p
    Aggr :: AggrOp -> Thunk -> Expr' p
    AggrNested :: AggrOp -> (Lang' p) -> Expr' p
    Nest :: Lang' a -> Expr' a
    Pack :: {  packLabels :: [Var] } ->  Expr' p
deriving instance Eq Expr
deriving instance Ord Expr
deriving instance Show Expr
deriving instance Data Expr


instance TraverseP Expr'  where
   traverseP _ (Ref a) = pure (Ref a)
   traverseP _ (AThunk a) = pure $ AThunk a
   traverseP f (Proj t i e) = Proj t i <$> traverseP f e
   traverseP f (BOp t op a b) = BOp t op <$> traverseP f a <*> traverseP f b
   traverseP _ Unit = pure Unit
   traverseP f (Tuple es) = Tuple <$> traverse (traverseP f) es
   traverseP f (AggrNested op a) = AggrNested op <$> f a
   traverseP _ (Aggr _ _) = error "aggr"
   traverseP f (Nest o) = Nest <$> f o
   traverseP _ (Pack ls) = pure $ Pack ls
   -- traverseP f (Unpack e ls b) = Unpack <$> traverseP f e <*> pure ls <*> traverseP f b
(.==) :: Expr' p -> Expr' p -> Expr' p
(.==) a  b = BOp AnyType Eql (ValArg a) (ValArg b)
data AggrOp = SumT | MinT | MaxT
  deriving (Eq, Ord, Show, Data)
type Expr = Expr' 'Flat
data ExprType = EBase TypeRep | TupleTyp [ExprType] | ThunkTy [Fun] ExprType | AnyType
  deriving (Eq, Ord, Show)

instance Data ExprType where
    gfoldl _ z a@EBase {} = z a
    gfoldl k z (TupleTyp ls)       = z TupleTyp `k` ls
    gfoldl k z (ThunkTy fs t) = z ThunkTy `k` fs `k` t
    gfoldl _ z AnyType = z AnyType

    gunfold k z c
      = case constrIndex c of
        4 -> z AnyType
        3 -> k (k (z ThunkTy))
        2 -> k (z TupleTyp)
        1 -> z AnyType
        _ -> error "illegal constructor index"

    toConstr EBase {} = eBaseConstr
    toConstr AnyType {} = eAnyTypeConstr
    toConstr TupleTyp {} = eTupleConstr
    toConstr ThunkTy {} = thunkConstr

    dataTypeOf _ = exprTypeDataType

eBaseConstr, eAnyTypeConstr, eTupleConstr, thunkConstr :: Constr
eBaseConstr = mkConstr exprTypeDataType "EBase" [] Prefix
eAnyTypeConstr = mkConstr exprTypeDataType "AnyType" [] Prefix
eTupleConstr = mkConstr exprTypeDataType "Tuple" [] Prefix
thunkConstr = mkConstr exprTypeDataType "Thunk" [] Prefix
exprTypeDataType :: DataType
exprTypeDataType = mkDataType "ExprType" [eBaseConstr, eTupleConstr, thunkConstr]

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
        _ -> error "illegal constructor index"
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
langDataType = mkDataType "Lang" [bindConstr, filterConstr, returnConstr, opLangConstr, lRefConstr, fBindConstr, asyncBindConstr]

    
instance TraverseP Lang' where
    traverseP f (Bind l v l') = Bind <$> traverseP f l <*> pure  v <*> traverseP f l'
    traverseP f (Filter e l) = Filter <$> traverseP f e <*> traverseP f l
    traverseP f (Return e) = Return <$> traverseP f e
    traverseP f (OpLang op) = OpLang <$> traverseP f op
    traverseP _ (LRef v) = pure (LRef v)
    traverseP f (AsyncBind ls l) = AsyncBind ls <$> traverseP f l
    traverseP _ (FBind _ _) = undefined -- FBind <$> (traverseP f l) <*> (traverseP f . g)
data OpLang' (t::Phase)
  = Opaque String
  | Union (Lang' t) (Lang' t)
  | Unpack { unpack :: Lang' t, labels :: [Var], unpackBody :: Lang' t }
  | Lookup { lookupTable :: Source, keys :: [Var], assigned :: Var, lookupBody :: Lang' t}
type OpLang = OpLang' 'Flat
deriving instance Eq OpLang
deriving instance Ord OpLang
deriving instance Show OpLang
deriving instance Data OpLang
instance TraverseP OpLang' where
    traverseP _ (Opaque s) = pure $ Opaque s
    traverseP f (Union l l') = Union <$> traverseP f l <*> traverseP f l'
    traverseP f (Unpack a b c) = Unpack <$> f a <*> pure b <*> f c
    traverseP f (Lookup a b c d) = Lookup a b c <$> f d
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


instance Pretty Var where
   pretty (Var v n) = pretty n <> "_" <> pretty v
instance Pretty Fun where
   pretty (Fun f) = pretty f
instance Pretty Source where
    pretty (Source s) = pretty s
instance Pretty ExprType where
    pretty (EBase t) = pretty (show t)
    pretty (TupleTyp ts) = parens (hsep (punctuate comma (map pretty ts)))
    pretty (ThunkTy fs t) = parens (hsep (punctuate comma (map pretty fs)) <+> "->" <+> pretty t)
    pretty AnyType = "AnyType"
instance Pretty BOp where
    pretty Eql = "=="
instance Pretty SomeArg where
    pretty (ValArg e) = pretty e
    pretty (ThunkArg f _ es) = pretty f <> parens (hsep (punctuate comma (map pretty es)))
instance Pretty AggrOp where
    pretty SumT = "SUM"
    pretty MinT = "MIN"
    pretty MaxT = "MAX"
instance Pretty Expr where
    pretty (Ref t) = pretty t
    pretty (Proj t i e) = pretty e <> "." <> pretty i <> "::" <> pretty t
    pretty (BOp t op e1 e2) = pretty e1 <+> pretty op <+> pretty e2 <> "::" <> pretty t
    pretty Unit = "()"
    pretty (Aggr op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (AggrNested op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (Tuple es) = tupled (map pretty es)
    pretty (AThunk a) = pretty a
    pretty (Nest a) = "Nest" <+> pretty a
    pretty (Pack a) = "Pack" <> tupled (map pretty a)
instance Pretty Lang where
    pretty (Bind a b c) = group $ nest 2 $ "for" <+> pretty b <+> "in" <+> align (pretty a) <+> "{" <> nest 2 (line <> pretty c) <> line <> "}"
    pretty (LRef v) = "*" <> pretty v
    pretty (Filter p c) = "when" <+> parens (pretty p) <+> pretty c
    pretty (AsyncBind lets bod) = group $ ("async" <+> align (encloseSep open close sep [maybe "" (\x -> pretty x <> " ") op <> pretty k <+> "=" <+> pretty v | (k,op, v) <- lets])) <> line <> "in" <+> pretty bod
      where
        open = flatAlt "" "{ "
        close = flatAlt "" " }"
        sep = flatAlt "" "; "
    -- pretty (Comprehend bs lets ps ps2 t e) =
            
        
    --         align(
    --             "for" <+>
    --             pBinds bs <>
    --             hcat [
    --         pList "let" lets, 
    --         pList "where" ps ,
    --         pList "where2" ps2
    --          ] <> pOut e <> pTyp t)
    --   where
    --     pBinds out = align (hsep . punctuate "," . map pBind $ out) <> line
    --     pBind (v, t) = pretty v <+> "in" <+> pretty t
    --     pList _ [] = mempty
    --     pList s ls =  s <+> pretty ls <> line
    --     pTyp AnyType = mempty
    --     pTyp t = " ::" <+> pretty t
    --     pOut e = " yield" <+> pretty e
    pretty (Return e) = "yield" <+> pretty e
    pretty (OpLang o) = pretty o
instance Pretty OpLang where
    pretty (Opaque s) = "#" <> pretty s
    pretty (Union a b) = "Union" <+> pretty a <+> pretty b
    pretty (Unpack a v c) = group $ "let"<+> align ("Pack" <> align (tupled (map pretty v)) <> softline <> "=" <+> pretty a) <> line' <> "in" <+> pretty c
    pretty (Lookup table keys assigned body) = group $ "lookup" <+> pretty assigned <+> ":=" <+> align (pretty table <> pretty keys) <+> line' <> "in" <+> pretty body
-- instance Pretty a => Pretty (Typed a) where
--     pretty (Typed a AnyType) = pretty a
--     pretty (Typed a t) = pretty a <> "::" <> pretty t
instance Pretty a => Pretty (TopLevel' a) where
    pretty (TopLevel ds root) = "let " <> align (vsep (prettyAssignments ds)) <> line <> "in " <> pretty root
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
    body <- normalize (f (AThunk $ Thunk (Source local) []))
    tellGlobal @RecLang var (Bind (LRef head) local (LRef body))
  pure var
normalize w = do
  key <- stableName w
  let var = Var key "v"
  doOnce key (tellGlobal @RecLang var =<< traverseP (fmap LRef . normalize) w)
  pure var
     -- go :: RecLang -> m (Lang' Var)
     -- go (Bound (Bound a b) e) = go $ Bound a (\a' -> Bound (b a') e)
     -- go (Bound (Guard g) e) = do
     --    g <- traverse normalize g
     --    Filter g <$> go (e Unit)
     -- go (Bound m e) = do
     --   ms <- normalize m
     --   v <- freshName
     --   let var = Var v "l"
     --   Bind ms var <$> go (e (Ref (VRef var)))
     -- go (Guard g) = go (Bound (Guard g) (\_ -> RecLang $ Return Unit))
     -- go (RecLang (Return a)) = do
     --     Return <$> traverse normalize a
     -- go a = do
     --   var <- normalize a
     --   pure $ Return (Ref var)
--      go guards acc (Bound (Guard g) e) = do
--         g' <- traverse normalize g
--         go (g':guards) acc (e Unit)
--      go guards acc (Bound body fun) = do
--         varId <- stableName fun
--         bodyId <- normalize body
--         let var = Var varId "l"
--         go guards ((var,Typed bodyId AnyType):acc) (fun (Ref $ Typed (VRef var) AnyType))
--      -- bit ugly, and should be handled by the inliner later anyway
--      -- go guards acc (RecLang (Return (Ref (Typed (VRef v) t)))) = pure $ Comprehend (reverse acc) [] guards [] t (Ref (Typed v t))
--      go guards acc (RecLang (OpLang o)) = do
--          go guards acc (Bound (RecLang $ OpLang o) (RecLang . Return))
--      go guards acc (RecLang i) =
--          traverse normalize i >>= \case
--            Return o -> pure $ Comprehend (reverse acc) [] guards [] AnyType o
--            c@Comprehend {} -> pure $ c { cBound = reverse acc <> cBound c, cPred = guards <> cPred c }
--            OpLang _ -> error "Impossible"
--      go guards acc (VRef v) = go guards acc (Bound (VRef v) (RecLang . Return))
--        -- l <- freshName
--        -- let loc = Var l "v"
--        -- pure $ Comprehend (reverse $ (loc,Typed v AnyType):acc) [] guards [] AnyType (Ref $ Typed loc AnyType)
--      go guards acc (Guard g) = go guards acc (Bound (Guard g) (\_ -> RecLang $ Return Unit))
    -- v <- normalize e
    -- normalize (f (Ref (Typed v AnyType)))
instance (MonadRef m, MonadGlobals RecLang m) => MuRef RecLang m where
    type DeRef RecLang = Lang
    type Key RecLang = Var
    makeKey _ i = Var i "v"
    mapDeRef _ _ = undefined -- traverse normalize
    --   where
    --     dyn = toDyn k
    --     var = undefined dyn :: Var
toTopLevel :: RecLang -> TopLevel' Lang
toTopLevel l = unsafePerformIO $ do
   (var, tl) <- runStable $ runStateT (normalize l) (TopLevel M.empty (Source $ Var 0 "<unknown_root>"))
   pure tl { root = Source var }

type TopLevel = TopLevel' Lang

data TypeEnv = TE { tableTys :: LM.Map Var ExprType, funTys :: LM.Map Fun ExprType }
  deriving (Eq, Ord, Show, Data)
type ScopeEnv = M.Map Var ExprType
-- etyOf :: Expr' e -> ExprType
-- etyOf = \case
--   Ref var -> var
--   Proj ety _ _ -> ety
--   BOp ety _ _ _ -> ety
--   _ -> error "todo"
-- ltyOf :: Lang' a -> ExprType
-- ltyOf = \case
--   -- Comprehend _ _ _ _ ety _ -> ety
--   Return e -> etyOf e
--   _ -> error "todo"

freeVarsQ :: Data a => a -> S.Set Var
freeVarsQ = runQ $
     tryQuery (\_ -> \case
       LRef @'Flat v -> Just (S.singleton v)
       _ -> Nothing)
 |||
     tryQuery (\_ -> \case
       (Ref v::Expr) ->   Just (S.singleton v)
       _ -> Nothing)
 |||
     tryQuery (\rec -> \case
       (Thunk (Source v) ls) ->  Just (S.singleton v <> rec ls))
 ||| tryQuery (\rec -> \case
       (w@(AsyncBind a _) :: Lang) -> Just (S.difference (mconcat $ gmapQ rec w) (S.fromList [v|(v,_,_) <-  a]))
       _ -> Nothing)
 ||| tryQuery (\rec -> \case
       (w@(Unpack _ b _) :: OpLang) -> Just (S.difference (mconcat $ gmapQ rec w) (S.fromList b))
       _ -> Nothing)
 ||| tryQuery (\rec -> \case
       (w@Bind {} :: Lang) -> Just (S.delete (boundVar w) (mconcat $ gmapQ rec w))
       _ -> Nothing)
 ||| recurse
