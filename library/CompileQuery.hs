{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
module CompileQuery where
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad.State
import Data.Data
import qualified Data.Map.Lazy as LM
import Data.Kind (Type)
import Data.Reify
import GHC.IO (unsafePerformIO)
import Prettyprinter
import Prettyprinter.Render.String (renderString)


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

data SomeArg' p = ValArg (Expr' p) | CollArg p | ThunkArg Source ExprType [Expr' p]
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
type SomeArg = SomeArg' Var
-- data Typed Var = Typed Var { tvVar :: Var, tvType :: ExprType }
--   deriving (Eq, Ord, Show, Data)
data Typed a = Typed { tyData :: a, tyType :: ExprType }
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
data Expr' p = Ref (Typed p)
             | Proj ExprType Int (Expr' p)
             | BOp ExprType BOp (SomeArg' p) (SomeArg' p)
             | Unit
             | Tuple [Expr' p]
             | Aggr AggrOp (SomeArg' p)
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
(.==) :: Expr' p -> Expr' p -> Expr' p
(.==) a  b = BOp AnyType Eql (ValArg a) (ValArg b)
data AggrOp = SumT | MinT | MaxT
  deriving (Eq, Ord, Show, Data)
type Expr = Expr' Var
data ExprType = EBase TypeRep | TupleTyp [ExprType] | Thunk [Fun] ExprType | AnyType
  deriving (Eq, Ord, Show)

instance Data ExprType where
    gfoldl _ z a@EBase {} = z a
    gfoldl k z (TupleTyp ls)       = z TupleTyp `k` ls
    gfoldl k z (Thunk fs t) = z Thunk `k` fs `k` t
    gfoldl _ z AnyType = z AnyType

    gunfold k z c
      = case constrIndex c of
        4 -> z AnyType
        3 -> k (k (z Thunk))
        2 -> k (z TupleTyp)
        1 -> z AnyType
        _ -> error "illegal constructor index"

    toConstr EBase {} = eBaseConstr
    toConstr AnyType {} = eAnyTypeConstr
    toConstr TupleTyp {} = tupleConstr
    toConstr Thunk {} = thunkConstr

    dataTypeOf _ = exprTypeDataType

eBaseConstr, eAnyTypeConstr, tupleConstr, thunkConstr :: Constr
eBaseConstr = mkConstr exprTypeDataType "EBase" [] Prefix
eAnyTypeConstr = mkConstr exprTypeDataType "AnyType" [] Prefix
tupleConstr = mkConstr exprTypeDataType "Tuple" [] Prefix
thunkConstr = mkConstr exprTypeDataType "Thunk" [] Prefix
exprTypeDataType :: DataType
exprTypeDataType = mkDataType "ExprType" [eBaseConstr, tupleConstr, thunkConstr]

newtype Uniq = Uniq Int
  deriving (Eq, Show, Ord, Data)
data BOp = Eql
  deriving (Eq, Ord, Show, Data)
data Lang' (t :: Type) where
  Comprehend :: {
      cBound :: [(Var, Typed t)],
      cLet :: [(Var, Expr' t)],
      cPred :: [Expr' t],
      cPred2 :: [Expr' t],
      eTyp :: ExprType,
      cOut :: Expr' t
    } -> Lang' t
  Return :: (Expr' t) -> Lang' t
  OpLang :: OpLang t -> Lang' t
  -- | LOp LOp (Typed t) (Typed t)
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
data OpLang t = Opaque String | Union t t
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
type Lang = Lang' Var
data RecLang
    = RecLang { unRecLang :: Lang' RecLang }
    | Bound RecLang (Expr' RecLang -> RecLang )
    | VRef Var
    | Guard { gPred :: Expr' RecLang }
newtype Source = Source { unSource :: Var}
  deriving (Eq, Ord, Show, Data)
data Var = Var { uniq :: Int, name :: String }
  deriving (Eq, Ord, Show, Data)
newtype Fun = Fun { unFun :: Var}
  deriving (Eq, Ord, Show, Data)
data Out' p = Out { target :: Source, expr :: Expr' p }
  deriving (Eq, Ord, Show, Data)
type Out = Out' Var
type Local = Typed Var
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
    pretty (Thunk fs t) = parens (hsep (punctuate comma (map pretty fs)) <+> "->" <+> pretty t)
    pretty AnyType = "AnyType"
instance Pretty BOp where
    pretty Eql = "=="
instance Pretty a => Pretty (SomeArg' a) where
    pretty (ValArg e) = pretty e
    pretty (CollArg v) = pretty v
    pretty (ThunkArg f _ es) = pretty f <> parens (hsep (punctuate comma (map pretty es)))
instance Pretty AggrOp where
    pretty SumT = "SUM"
    pretty MinT = "MIN"
    pretty MaxT = "MAX"
instance Pretty a => Pretty (Expr' a) where
    pretty (Ref t) = pretty t
    pretty (Proj t i e) = pretty e <> "." <> pretty i <> "::" <> pretty t
    pretty (BOp t op e1 e2) = pretty e1 <+> pretty op <+> pretty e2 <> "::" <> pretty t
    pretty Unit = "()"
    pretty (Aggr op v) = pretty op <> "(" <>  pretty v <> ")"
    pretty (Tuple es) = tupled (map pretty es)
instance Pretty a => Pretty (Lang' a) where
    pretty (Comprehend bs lets ps ps2 t e) =
            
        
            align(
                "for" <+>
                pBinds bs <>
                hcat [
            pList "let" lets, 
            pList "where" ps ,
            pList "where2" ps2
             ] <> pOut e <> pTyp t)
      where
        pBinds out = align (hsep . punctuate "," . map pBind $ out) <> line
        pBind (v, t) = pretty v <+> "in" <+> pretty t
        pList _ [] = mempty
        pList s ls =  s <+> pretty ls <> line
        pTyp AnyType = mempty
        pTyp t = " ::" <+> pretty t
        pOut e = " yield" <+> pretty e
    pretty (Return e) = "Return" <+> pretty e
    pretty (OpLang o) = "OpLang" <+> pretty o
instance Pretty a => Pretty (OpLang a) where
    pretty (Opaque s) = "Opaque" <+> pretty s
    pretty (Union a b) = "Union" <+> pretty a <+> pretty b
instance Pretty a => Pretty (Typed a) where
    pretty (Typed a AnyType) = pretty a
    pretty (Typed a t) = pretty a <> "::" <> pretty t
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

class FreeVars s where
    freeVars :: s -> S.Set Local
instance (FreeVars Lang, Monad m) => MonadGlobals RecLang (StateT (TopLevel' Lang) m)  where
  tellGlobal k v = modify' $ \tl -> tl { defs = M.insert (Source k) (S.toList $ freeVars v, v) (defs tl) }

export :: (MonadGlobals RecLang m, MonadRef m) => Lang' Var ->  m Var
export val = do
    key <- stableName val
    let name = Var key "v"
    doOnce key (tellGlobal @RecLang name val)
    pure name

labelFor :: FreeVars (Lang' p) => Lang' p -> String
labelFor (OpLang (Opaque s)) = s  <> "s"
labelFor c@Comprehend {} 
  | freeVars c /= S.empty = "f"
labelFor _ = "v"
doOnce :: MonadRef m => Unique -> m () -> m ()
doOnce key m = do
    seen <- wasVisited key
    unless seen $ do
      markVisited key
      m

normalize :: forall m. (MonadGlobals RecLang m, MonadRef m) => RecLang -> m Var
normalize (VRef v) = pure v
normalize (RecLang (Return (Ref o))) = normalize (tyData o)
normalize w@(RecLang l) = do
  key <- stableName w
  let var = Var key "v"
  doOnce key (tellGlobal @RecLang var =<< traverse normalize l)
  pure var
normalize w@(Bound r k) = do
  key <- stableName w
  let var = Var key "v"
  doOnce key (tellGlobal @RecLang var =<< go [] [] (Bound r k))
  pure var
  where
     go :: [Expr] -> [(Var, Typed Var)] -> RecLang -> m (Lang' Var)
     go guards acc (Bound (Guard g) e) = do
        g' <- traverse normalize g
        go (g':guards) acc (e Unit)
     go guards acc (Bound body fun) = do
        varId <- stableName fun
        bodyId <- normalize body
        let var = Var varId "l"
        go guards ((var,Typed bodyId AnyType):acc) (fun (Ref $ Typed (VRef var) AnyType))
     -- bit ugly, and should be handled by the inliner later anyway
     -- go guards acc (RecLang (Return (Ref (Typed (VRef v) t)))) = pure $ Comprehend (reverse acc) [] guards [] t (Ref (Typed v t))
     go guards acc (RecLang (OpLang o)) = do
         go guards acc (Bound (RecLang $ OpLang o) (RecLang . Return))
     go guards acc (RecLang i) =
         traverse normalize i >>= \case
           Return o -> pure $ Comprehend (reverse acc) [] guards [] AnyType o
           c@Comprehend {} -> pure $ c { cBound = reverse acc <> cBound c, cPred = guards <> cPred c }
           OpLang _ -> error "Impossible"
     go guards acc (VRef v) = go guards acc (Bound (VRef v) (RecLang . Return))
       -- l <- freshName
       -- let loc = Var l "v"
       -- pure $ Comprehend (reverse $ (loc,Typed v AnyType):acc) [] guards [] AnyType (Ref $ Typed loc AnyType)
     go guards acc (Guard g) = go guards acc (Bound (Guard g) (\_ -> RecLang $ Return Unit))
    -- v <- normalize e
    -- normalize (f (Ref (Typed v AnyType)))
normalize (Guard _) = error "standalone guard not implemented yet"
instance (MonadRef m, MonadGlobals RecLang m) => MuRef RecLang m where
    type DeRef RecLang = Lang' Var
    type Key RecLang = Var
    makeKey _ i = Var i "v"
    mapDeRef _ _ = undefined -- traverse normalize
    --   where
    --     dyn = toDyn k
    --     var = undefined dyn :: Var
toTopLevel :: FreeVars Lang => RecLang -> TopLevel' Lang
toTopLevel l = unsafePerformIO $ do
   (var, tl) <- runStable $ runStateT (normalize l) (TopLevel M.empty (Source $ Var 0 "<unknown_root>"))
   pure tl { root = Source var }

type TopLevel = TopLevel' (Lang' Var)

data TypeEnv = TE { tableTys :: LM.Map Var ExprType, funTys :: LM.Map Fun ExprType }
  deriving (Eq, Ord, Show, Data)
type ScopeEnv = M.Map Var ExprType
etyOf :: Expr' e -> ExprType
etyOf = \case
  Ref var -> tyType var
  Proj ety _ _ -> ety
  BOp ety _ _ _ -> ety
  _ -> error "todo"
ltyOf :: Lang' a -> ExprType
ltyOf = \case
  Comprehend _ _ _ _ ety _ -> ety
  Return e -> etyOf e
  _ -> error "todo"
