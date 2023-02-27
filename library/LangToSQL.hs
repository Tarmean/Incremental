{-# LANGUAGE OverloadedRecordDot #-}
module LangToSQL where

import CompileQuery
import SQL
import qualified Data.Map as M


langToSQL :: Lang -> SQL
langToSQL (OpLang ol) = case ol of
  -- Group f t o b -> Group (langToSQL f) (langToSQL t)
langToSQL b@Bind {} = toSPJ emptySPJ b
langToSQL b = toSPJ emptySPJ b


emptySPJ :: SPJ
emptySPJ = SPJ mempty mempty mempty

toSPJ :: SPJ -> Lang -> SQL
toSPJ spj (Bind b v e) = toSPJ (spj { sources = (v,langToSQL b) : sources spj }) e
toSPJ spj (Filter p e) = toSPJ (spj { wheres = exprToSQL p : spj.wheres}) e
toSPJ spj (Return e) = case e of
  Tuple _ ls -> ASPJ $ spj {proj = M.fromList (zip ["f" <> show i | i <- [0::Int ..]] $ map exprToSQL ls)}
  _ -> error "Illegal return"
toSPJ spj (AsyncBind {}) = error "Illegal async bind"
toSPJ spj (LRef {}) = error "LRef in return position"
toSPJ spj (OpLang ol) = case ol of
   Opaque {} -> error "Compilation failure"
   Let {} -> error "Compilation failure"
   Unpack {} -> error "Compilation failure"
   Call {} -> error "Compilation failure"
   Force {} -> error "Compilation failure"
   HasType _ l _ -> toSPJ spj l
   o -> makeLateral spj o

makeLateral :: SPJ -> OpLang -> SQL
makeLateral _spj _ol = error "Not Implemented yet" 
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
