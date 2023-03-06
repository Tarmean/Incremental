{-# LANGUAGE OverloadedRecordDot #-}
module LangToSQL where

import CompileQuery
import qualified CompileQuery as Q
import SQL
import qualified Data.Map as M
import qualified Data.Set as S


langToSQL :: Lang -> SQL
langToSQL (OpLang (Fold bound ctx ret src))
    | not (flatGroup ctx) = error "Fold returning nested aggregates not efficiently supported (in sql)"
    | otherwise = GroupQ (exprsToSQL $ S.toList (outerKeys ctx)) (ASPJ SPJ {  sources = [(bound, langToSQL src)], wheres = [], proj = aggrToSQL ret})
langToSQL (OpLang (Distinct src)) = DistinctQ (langToSQL src)
langToSQL (OpLang(Opaque tableName tableMeta)) = Table tableMeta tableName
langToSQL (OpLang (HasType _ s _)) = langToSQL s
langToSQL (LRef s) = toTable s
langToSQL b@Bind {} = toSPJ emptySPJ b
langToSQL b = toSPJ emptySPJ b


emptySPJ :: SPJ
emptySPJ = SPJ mempty mempty mempty

toSPJ :: SPJ -> Lang -> SQL
toSPJ spj (Bind b v e) = toSPJ (spj { sources = (v,langToSQL b) : sources spj }) e
toSPJ spj (Filter p e) = toSPJ (spj { wheres = exprToSQL p : spj.wheres}) e
toSPJ spj (Return e) = case e of
  Tuple _ ls -> ASPJ $ spj {proj = toFieldMap $ map exprToSQL ls}
  _ -> error ("LangToSQL: return not a tuple: " <> prettyS spj <> ", " <> prettyS e)
toSPJ _spj (AsyncBind {}) = error "Illegal async bind"
toSPJ _spj l@(LRef {}) = error ("LRef in return position" <> prettyS (_spj, l))
toSPJ spj (OpLang ol) = error ("Compilation failure" <> prettyS (spj, ol))
   -- Let {} -> error "Compilation failure"
   -- Unpack {} -> error "Compilation failure"
   -- Call {} -> error "Compilation failure"
   -- Force {} -> error "Compilation failure"
   -- HasType _ l _ -> toSPJ spj l
   -- o -> makeLateral spj o

makeLateral :: SPJ -> OpLang -> SQL
makeLateral _spj _ol = error ("makeLateral, Not Implemented yet" <> prettyS (_spj, _ol))

aggrToSQL :: CompileQuery.AnAggregate -> M.Map AField SQL.Expr
aggrToSQL = toFieldMap . toExpressions



exprsToSQL :: [CompileQuery.Expr] -> [SQL.Expr]
exprsToSQL = concatMap go 
  where
    go (Q.Tuple _ ls) = concatMap go ls
    go e = [exprToSQL e]
exprToSQL :: CompileQuery.Expr -> SQL.Expr
exprToSQL (Proj 0 1 (Q.Singular e)) = SQL.Singular (langToSQL e)
exprToSQL (Proj i _ (Q.Ref v)) = SQL.Ref v (toField  i)
exprToSQL (Q.BOp op l r) = SQL.BOp op (exprToSQL l) (exprToSQL r)
exprToSQL (Lookup sym args) = SQL.Singular $ ASPJ $ SPJ
  { proj = toFieldMap (fmap (SQL.Ref var) (toField <$> [2]))
  , sources = [(var, toTable (Q.unSource sym))]
  , wheres = zipWith (SQL.BOp Q.Eql) (fmap exprToSQL args) (fmap (SQL.Ref var) (toField <$> [0::Int ..]))
  }
  where var = Var 99 "t"
exprToSQL (Q.Lit l) = SQL.Lit l
exprToSQL o = error ("Unimplemented exprToSQL: " <> prettyS o)

toTable :: Var -> SQL
toTable sym = Table (Q.TableMeta (Q.FD [["f2"]]) ["f0", "f1", "f2"]) (prettyS sym)

toExpressions :: CompileQuery.AnAggregate -> [SQL.Expr]
toExpressions (CompileQuery.AggrTuple ls) = concatMap toExpressions ls
toExpressions (CompileQuery.BaseAg op e) = pure (AggrOp op (exprToSQL e))
toExpressions _ = error "Unimplemented"

