{-# LANGUAGE QualifiedDo #-}
module Test where
import qualified MonadSyntax as M
import CompileQuery


table :: String -> RecLang
table s = VRef (Var 0 s)

testQ :: RecLang
testQ = M.do
   a <- table "user"
   _ <- testQ
   M.return a
  
   
testFlat :: RecLang
testFlat = M.do
   let a = table "user"
   _ <- a
   _ <- a
   o <- table "bar"
   M.pure o
