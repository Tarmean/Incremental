{-# LANGUAGE OverloadedRecordDot #-}
module LangToSQL where

import CompileQuery
import SQL
import qualified Data.Map as M


langToSQL :: Lang -> SQL
langToSQL b@Bind {} = (toSPJ emptySPJ b)

emptySPJ :: SPJ
emptySPJ = SPJ mempty mempty mempty

toSPJ :: SPJ -> Lang -> SQL
toSPJ spj (Bind b v e) = toSPJ (spj { sources = (v,langToSQL b) : sources spj }) e
toSPJ spj (Filter p e) = toSPJ (spj { wheres = exprToSQL p : spj.wheres}) e
toSPJ spj (Return e) = case e of
  Tuple ls -> ASPJ $ spj {proj = M.fromList (zip ["f" <> show i | i <- [0::Int ..]] $ map exprToSQL ls)}
  _ -> error "Illegal return"
toSPJ spj (AsyncBind {}) = error "Illegal async bind"
-- toSPJ spj (LRef {}) = error "Illegal lref"
-- toSPJ spj (OpLang ol) = case ol of
--     Opaque name ml -> Table ml name
--     Group _ _ ops s -> if spj == emptySPJ then handleGroup ops (langToSQL s) else error "Illegal group op"

handleGroup :: Int -> [AggrOp] -> SQL -> SQL
handleGroup ags l = undefined

-- spj == emptySPJ
                   -- then out else error "Illegal group op"
        -- where
           
          

exprToSQL :: CompileQuery.Expr -> SQL.Expr
exprToSQL = undefined
