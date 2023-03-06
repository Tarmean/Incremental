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
import Data.Foldable (foldrM)
import qualified CompileQuery as Q

data SPJ = SPJ { sources :: [(Var, SQL)], wheres :: [Expr], proj :: M.Map AField Expr }
  deriving (Show, Eq, Ord, Data, Generic)

data SQL = ASPJ SPJ
         | GroupQ { groups :: [Expr], source :: SQL }
         | Table TableMeta String
         | Slice { limit :: Maybe Int,  offset :: Maybe Int, source :: SQL }
         | DistinctQ { source :: SQL }
         | OrderBy { by :: [Expr], source :: SQL }
  deriving (Show, Eq, Ord, Data, Generic)
type AField = String

toField :: Int -> String
toField i = "f" <> show i
toFieldMap :: [SQL.Expr] -> M.Map AField SQL.Expr
toFieldMap = M.fromList . zip (toField <$> [0::Int ..])

data Expr = BOp Q.BOp Expr Expr | Ref Var AField | AggrOp Q.AggrOp Expr | Singular SQL | Lit Q.ALit
  deriving (Show, Eq, Ord, Data, Generic)
instance Pretty SQL where
    pretty (Table _ name) = pretty name
    pretty (GroupQ g e) = align $ group $ pretty e <> line <> "GROUP BY " <> tupled (map pretty g)
    pretty (ASPJ spj) = pretty spj
    pretty (DistinctQ spj) = "DISTINCT " <> pretty spj
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

instance Pretty Expr where
    pretty (BOp f a b) = pretty a <+> pretty f <+> pretty b
    pretty (Ref v s) = pretty v <> "." <> pretty s
    pretty (AggrOp Q.ScalarFD o) = pretty o
    pretty (AggrOp top o) = pretty top <> parens (pretty o)
    pretty (Singular sql) = parens (pretty sql)
    pretty (Lit a) = pretty a

substSQLs :: Data a => M.Map Var (M.Map AField Expr) -> a -> a
substSQLs m a
  | M.null m = a
substSQLs fields a = runT' (
   tryTransM @Expr (\rec -> \case
       Ref v' f
         -> case fields M.!? v' of
            Nothing -> Nothing
            Just m' -> case m' M.!? f  of
               Just f' -> Just (rec f')
               Nothing -> error ("substSQL: field not found: " <> show (m', f, fields))
       _ -> Nothing)
  ||| recurse) a
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

type SubstEnv = M.Map Var (M.Map AField Expr)
flattenSPJ1 :: Var -> SQL -> SPJ -> Writer SubstEnv SPJ
flattenSPJ1 source (ASPJ (SPJ {..})) parent = do
  tell (M.singleton source proj)
  pure $ parent
      & #wheres <>~ wheres
      & #sources <>~ sources
flattenSPJ1 source sql parent = pure $ parent & #sources <>~ [(source, sql)]
flattenSPJ :: SPJ -> Maybe (Writer SubstEnv SPJ)
flattenSPJ (SPJ { sources,.. }) = case runWriter $ foldrM (uncurry flattenSPJ1) (SPJ {sources=mempty,..}) sources of
    (spj, m) 
      | M.null m -> Nothing
      | otherwise -> Just (substSQLs m spj <$ tell m)


projMap :: SQL -> Maybe SQL
projMap (ASPJ SPJ { sources = [(k,v)], proj, wheres }) = mapSPJ transSPJ v
 where
  transSPJ spj = spj { proj = substSQL k spj.proj proj, wheres = spj.wheres <> substSQL k spj.proj wheres }
projMap _ = Nothing

-- | Fixme:
-- This is used to move joins inside a complex subquery.
-- We should only do this if the join
-- - Doesn't use positional logic such as window functions or sql procs
-- - Doesn't use lateral joins because otherwise we 'infect' non-lateral subqueries
mapSPJ :: (SPJ -> SPJ) -> SQL -> Maybe SQL
mapSPJ f (ASPJ s)= Just $ ASPJ (f s)
mapSPJ f (GroupQ ons c) = GroupQ ons <$> mapSPJ f c
mapSPJ _ _ = Nothing

traverseSPJ :: Applicative m => (SPJ -> m SPJ) -> SQL -> m SQL
traverseSPJ f (ASPJ s)= ASPJ <$> f s
traverseSPJ f (GroupQ ons c) = GroupQ ons <$> traverseSPJ f c
traverseSPJ f (DistinctQ c) = DistinctQ <$> traverseSPJ f c
traverseSPJ f (Slice l r c) = Slice l r <$> traverseSPJ f c
traverseSPJ f (OrderBy by c) = OrderBy by <$> traverseSPJ f c
traverseSPJ _ t@Table{} = pure t

selectOf :: SQL -> M.Map AField Expr
selectOf (ASPJ SPJ { proj }) = proj
selectOf (GroupQ _ons c) = selectOf c
selectOf (DistinctQ c) = selectOf c
selectOf (Slice _l _r c) = selectOf c
selectOf (OrderBy _by c) = selectOf c
selectOf (Table meta name) = toFieldMap [ Ref (Var 0 name) f | f <- fields meta ]
traverseSPJ_ :: Applicative m => (SPJ -> m ()) -> SQL -> m ()
traverseSPJ_ f (ASPJ s)= f s
traverseSPJ_ f (GroupQ _ons c) = traverseSPJ_ f c
traverseSPJ_ f (DistinctQ c) = traverseSPJ_ f c
traverseSPJ_ f (Slice _l _r c) = traverseSPJ_ f c
traverseSPJ_ f (OrderBy _by c) = traverseSPJ_ f c
traverseSPJ_ _ Table{} = pure ()


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
doFlattens a = substSQLs sub out
  where
    -- it me
    theTrans = recurse >>> (tryTrans_ flattenGroupBy ||| tryTrans_ projMap ||| tryTrans_ sinkWhere ||| tryTransM_ flattenSPJ)
    (out, sub) = runWriter $ runT theTrans a
