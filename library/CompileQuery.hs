{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ApplicativeDo #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module CompileQuery where
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Control.Monad.State
import Control.Monad.Trans.Elevator
import OpenRec
import Control.Monad.Writer.Strict (WriterT(..))
import Data.Data
import qualified Data.Map.Lazy as LM
import Control.Monad.Identity (Identity(..))
import Data.Bifunctor (Bifunctor(second))
import Control.Monad.Reader (ask, local, runReader)
import Data.Kind (Type)
import Data.Reify
import GHC.IO (unsafePerformIO)
import Prettyprinter
import Prettyprinter.Render.String (renderString)



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

data SomeArg' p = ValArg (Expr' p) | CollArg (Lang' p) | ThunkArg Fun ExprType [Expr' p]
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
type SomeArg = SomeArg' Var
-- data Typed Var = Typed Var { tvVar :: Var, tvType :: ExprType }
--   deriving (Eq, Ord, Show, Data)
data Typed a = Typed { tyData :: a, tyType :: ExprType }
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
data Expr' p = Ref (Typed p) | Proj ExprType Int (Expr' p) | BOp ExprType BOp (SomeArg' p) (SomeArg' p)
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
type Expr = Expr' Var
data ExprType = EBase TypeRep | Tuple [ExprType] | Thunk [Fun] ExprType | AnyType
  deriving (Eq, Ord, Show)

instance Data ExprType where
    gfoldl _ z a@EBase {} = z a
    gfoldl k z (Tuple ls)       = z Tuple `k` ls
    gfoldl k z (Thunk fs t) = z Thunk `k` fs `k` t
    gfoldl _ z AnyType = z AnyType

    gunfold k z c
      = case constrIndex c of
        4 -> z AnyType
        3 -> k (k (z Thunk))
        2 -> k (z Tuple)
        1 -> z AnyType
        _ -> error "illegal constructor index"

    toConstr EBase {} = eBaseConstr
    toConstr AnyType {} = eAnyTypeConstr
    toConstr Tuple {} = tupleConstr
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
  -- | LOp LOp (Typed t) (Typed t)
  deriving (Eq, Ord, Show, Data, Functor, Foldable, Traversable)
type Lang = Lang' Var
data RecLang = RecLang { unRecLang :: Lang' RecLang } | Bound RecLang (Expr' RecLang -> RecLang) | VRef Var
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
  defs :: M.Map Source p,
  funs :: M.Map Fun  ([Local], p),
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
    pretty (Tuple ts) = parens (hsep (punctuate comma (map pretty ts)))
    pretty (Thunk fs t) = parens (hsep (punctuate comma (map pretty fs)) <+> "->" <+> pretty t)
    pretty AnyType = "AnyType"
instance Pretty BOp where
    pretty Eql = "="
instance Pretty a => Pretty (SomeArg' a) where
    pretty (ValArg e) = pretty e
    pretty (CollArg v) = pretty v
    pretty (ThunkArg f _ es) = pretty f <> parens (hsep (punctuate comma (map pretty es)))
instance Pretty a => Pretty (Expr' a) where
    pretty (Ref (Typed v t)) = pretty v <> "::" <> pretty t
    pretty (Proj t i e) = pretty e <> "." <> pretty i <> "::" <> pretty t
    pretty (BOp t op e1 e2) = pretty e1 <+> pretty op <+> pretty e2 <> "::" <> pretty t
instance Pretty a => Pretty (Lang' a) where
    pretty (Comprehend bs lets ps ps2 t e) = "Comprehend" <+> pretty bs <+> pretty lets <+> pretty ps <+> pretty ps2 <+> pretty t <+> pretty e
    pretty (Return e) = "Return" <+> pretty e
instance Pretty a => Pretty (Typed a) where
    pretty (Typed a t) = pretty a <> "::" <> pretty t
instance Pretty a => Pretty (TopLevel' a) where
    pretty (TopLevel ds fs root) = "let " <> align (vsep (prettyAssignments ds <> prettyAssignments  fs)) <> line <> "in " <> pretty root
      where

        prettyAssignments m = [pretty k <+> "=" <+> pretty v | (k, v) <- M.toList m]

prettyS :: Pretty a => a -> String
prettyS = renderString . layoutPretty defaultLayoutOptions . pretty

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . prettyS

instance Monad m => MonadGlobals RecLang (StateT (TopLevel' Lang) m)  where
  tellGlobal k v = modify' $ \tl -> tl { defs = M.insert (Source k) v (defs tl) }
instance (MonadRef m, MonadGlobals RecLang m) => MuRef RecLang m where
    type DeRef RecLang = Lang' Var
    type Key RecLang = Var
    makeKey _ i = Var i "v"
    mapDeRef f (RecLang l) = case l of
      Comprehend ls lets g p t e -> do
        ls <- traverse (traverse (traverse f)) ls
        lets <- traverse (traverse (traverse f)) lets
        g <- traverse (traverse f) g
        p <- traverse (traverse f) p
        e <- traverse f e
        pure (Comprehend ls lets g p t e)
      Return e -> Return <$> traverse f e
    mapDeRef f (Bound r k) = do
        let
          go :: [(Var, Typed Var)] -> RecLang -> m (Lang' Var)
          go acc (Bound body fun) = do
             varId <- stableName fun
             bodyId <- f body
             let var = Var varId "l"
             go ((var,Typed bodyId AnyType):acc) (fun (Ref $ Typed (VRef var) AnyType))
          -- go acc (RecLang (Comprehend {})) = pure $ Comprehend (reverse acc) [] [] [] t (Ref (Typed v t))
          go acc (RecLang (Return (Ref (Typed (VRef v) t)))) = pure $ Comprehend (reverse acc) [] [] [] t (Ref (Typed v t))
          go acc (RecLang i) =
              traverse f i >>= \case
                Return o -> pure $ Comprehend (reverse acc) [] [] [] AnyType o
                c@Comprehend {} -> pure $ c { cBound = reverse acc <> cBound c }
          go acc (VRef v) = do
            l <- freshName
            let loc = Var l "v"
            pure $ Comprehend (reverse $ (loc,Typed v AnyType):acc) [] [] [] AnyType (Ref $ Typed loc AnyType)
        go [] (Bound r k)
    mapDeRef _ (VRef a) = pure $ Return $ Ref (Typed a AnyType)
    --   where
    --     dyn = toDyn k
    --     var = undefined dyn :: Var
toTopLevel :: RecLang -> TopLevel' Lang
toTopLevel l = unsafePerformIO $ do
   (var, tl) <- runStable $ runStateT (findNodes l) (TopLevel M.empty M.empty (Source $ Var 0 "<unknown_root>"))
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
ltyOf :: Lang' a -> ExprType
ltyOf = \case
  Comprehend _ _ _ _ ety _ -> ety
  Return e -> etyOf e
