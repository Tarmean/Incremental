{-# LANGUAGE OverloadedRecordDot, RecordWildCards #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE LambdaCase #-}
module SQL where
import qualified Data.Map.Strict as M
import Control.Monad.State
import Control.Lens
import Data.Generics.Labels ()
import OpenRec
import Data.Data
import GHC.Generics (Generic)


type Var = String

data SPJ = SPJ { sources :: [(Var, SQL)], wheres :: [Expr], proj :: !(M.Map AField Expr) }
  deriving (Show, Eq, Ord, Data, Generic)
data SQL = ASPJ SPJ | GroupQ { groups :: [Expr], source :: SQL }
  deriving (Show, Eq, Ord, Data, Generic)
type AField = String
data Expr = Eql Expr Expr | Ref Var AField
  deriving (Show, Eq, Ord, Data, Generic)

substSQL :: Data a => Var -> M.Map AField Expr -> a -> a
substSQL v fields = runT' (
   tryTrans_ @Expr \case
       Ref v' f
         | v == v'
         , Just f' <- fields M.!? f -> Just f'
       _ -> Nothing
  ||| recurse
        )

flattenSPJ1 :: Var -> SQL -> SPJ -> SPJ
flattenSPJ1 source (ASPJ (SPJ {..})) parent =
  substSQL source proj parent
  & #wheres <>~ wheres
  & #sources <>~ sources
flattenSPJ1 source sql parent = parent & #sources <>~ [(source, sql)]
flattenSPJ :: SPJ -> SPJ
flattenSPJ (SPJ { sources,.. }) = foldr (uncurry flattenSPJ1) (SPJ {sources=mempty,..}) sources


flattenGroupBy :: SQL -> Maybe SQL
flattenGroupBy (GroupQ ons (GroupQ ons2 c)) = Just $ GroupQ (ons2 <> ons) c
flattenGroupBy _ = Nothing


doFlattens :: Data a => a -> a
doFlattens = runT' $ recurse >>> (tryTrans flattenGroupBy ||| tryTrans_ (Just . flattenSPJ))
