{-# LANGUAGE OverloadedRecordDot, RecordWildCards #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module SQL where
import qualified Data.Map.Strict as M
import Control.Lens
import Data.Generics.Labels ()
import OpenRec
import Data.Data
import CompileQuery (TableMeta(..), Var(..))
import GHC.Generics (Generic)

import Prettyprinter
import qualified Data.Set as S
import Control.Monad.Trans.Writer.CPS
import Data.Either (partitionEithers)
import Data.Monoid (Any(..))
import Data.Foldable (foldrM)

data SPJ = SPJ { sources :: [(Var, SQL)], wheres :: [Expr], proj :: M.Map AField Expr }
  deriving (Show, Eq, Ord, Data, Generic)

data SQL = ASPJ SPJ
         | GroupQ { groups :: [Expr], source :: SQL }
         | Table TableMeta String
         | Slice { limit :: Maybe Int,  offset :: Maybe Int, source :: SQL }
         | OrderBy { by :: [Expr], source :: SQL }
  deriving (Show, Eq, Ord, Data, Generic)
type AField = String
data Expr = Eql Expr Expr | Ref Var AField | AggrOp AnOp Expr
  deriving (Show, Eq, Ord, Data, Generic)
data AnOp = SumO | MaxO
  deriving (Show, Eq, Ord, Data, Generic)
instance Pretty SQL where
    pretty (Table _ name) = pretty name
    pretty (GroupQ g e) = align $ group $ pretty e <> line <> "GROUP BY " <> tupled (map pretty g)
    pretty (ASPJ spj) = pretty spj
    pretty (Slice lim off e) = align $ group $ pretty e <> line <> limPart <> offPart
      where
        limPart = maybe "" (\l -> "LIMIT " <> pretty l) lim
        offPart = maybe "" (\o -> "OFFSET " <> pretty o) off
    pretty (OrderBy ord e) = align $ group $ pretty e <> line <> "ORDER BY " <> tupled (map pretty ord)
instance Pretty SPJ where
    pretty spj = group $ 
      align $ 
      "SELECT"
      <+> align (group $ hsep (punctuate ("," <> line') [pretty q <+> pretty var | (var,q) <- M.toList spj.proj]))
      <> line
      <> "FROM"
      <+> group (hsep (punctuate ("," <> line') [braceIfComplex q <+> pretty var | (var,q) <- spj.sources]))
      <> 
      if null spj.wheres then mempty else
      line <> "WHERE" <+> hsep (punctuate " AND " (map pretty spj.wheres))
      where
        isComplex (Table {}) = False
        isComplex _ = True
        braceIfComplex p
          | isComplex p = parens (pretty p)
          | otherwise = pretty p

instance Pretty AnOp where
    pretty SumO = "SUM"
    pretty MaxO = "MAX"
instance Pretty Expr where
    pretty (Eql a b) = pretty a <+> "=" <+> pretty b
    pretty (Ref v s) = pretty v <> "." <> pretty s
    pretty (AggrOp top o) = pretty top <> parens (pretty o)

substSQL :: Data a => Var -> M.Map AField Expr -> a -> a
substSQL v fields = runT' (
   tryTrans_ @Expr \case
       Ref v' f
         | v == v'
         -> case fields M.!? f of
           Just f' -> Just f'
           Nothing -> error ("substSQL: field not found: " <> show (v,f, fields))
       _ -> Nothing
  ||| recurse)

flattenSPJ1 :: Var -> SQL -> SPJ -> Writer Any SPJ
flattenSPJ1 source (ASPJ (SPJ {..})) parent = do
  tell (Any True)
  pure $ 
      substSQL source proj parent
      & #wheres <>~ wheres
      & #sources <>~ sources
flattenSPJ1 source sql parent = pure $ parent & #sources <>~ [(source, sql)]
flattenSPJ :: SPJ -> Maybe SPJ
flattenSPJ (SPJ { sources,.. }) = case runWriter $ foldrM (uncurry flattenSPJ1) (SPJ {sources=mempty,..}) sources of
    (spj, Any True) -> Just spj
    _ -> Nothing


projMap :: SQL -> Maybe SQL
projMap (ASPJ SPJ { sources = [(k,v)], proj, wheres }) = mapSPJ transSPJ v
 where
  transSPJ spj = spj { proj = substSQL k spj.proj proj, wheres = spj.wheres <> substSQL k spj.proj wheres }
projMap _ = Nothing

mapSPJ :: (SPJ -> SPJ) -> SQL -> Maybe SQL
mapSPJ f (ASPJ s)= Just $ ASPJ (f s)
mapSPJ f (GroupQ ons c) = GroupQ ons <$> mapSPJ f c
mapSPJ _ _ = Nothing


flattenGroupBy :: SQL -> Maybe SQL
flattenGroupBy (GroupQ ons (GroupQ ons2 c)) = Just $ GroupQ (ons2 <> ons) c
flattenGroupBy _ = Nothing

sinkWhere :: SQL -> Maybe SQL
sinkWhere (ASPJ spj) 
  | not (null sinkable) = Just (ASPJ spj')
  | otherwise = Nothing
  where
    (sinkables, wheres') = partitionEithers $ map isSinkable spj.wheres
    sinkable = M.fromListWith (<>) sinkables

    localBoundVars = S.fromList (map fst spj.sources)
    isSinkable expr
      | [x] <- S.toList (refsIn expr)
      , S.member x localBoundVars
      = Left (x,[expr])
      | otherwise = Right expr

    (sources', unSunk) = runWriter (traverse addSinkables spj.sources)
    spj' = spj { wheres = wheres' <> unSunk, sources = sources' }
    refsIn = runQ (tryQuery_ @Expr \case
      Ref s _ -> Just (S.singleton s)
      _ -> Nothing
     ||| recurse
     )

    addSinkables :: (Var, SQL) -> Writer [Expr] (Var, SQL)
    addSinkables (var,sql)
      | Just sunk <- sinkable M.!? var
      = case mapSPJ (\s -> s { wheres = s.wheres <> substSQL var s.proj sunk }) sql of
         Just upd -> pure (var, upd)
         Nothing -> tell sunk >> pure (var, sql)
      | otherwise = pure (var,sql)
sinkWhere _ = Nothing

doFlattens :: Data a => a -> a
doFlattens = runT' $ recurse >>> (tryTrans flattenGroupBy ||| tryTrans_ projMap ||| tryTrans_ sinkWhere ||| tryTrans_ flattenSPJ)
