{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
module Test where
import qualified MonadSyntax as M
import CompileQuery


table :: String -> RecLang
table s = OpLang (Opaque s)

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

testLeftNest :: RecLang
testLeftNest = M.do
   M.do
       _ <- table "user"
       table "foo"
   M.pure (nest $ table "bar")

testRightNest :: RecLang
testRightNest = M.do
   a <- table "user"
   let
    b = AggrNested SumT $ M.do
       f <- table "foo"
       guards (a .== f)
       M.pure f
   M.pure (Tuple [a, b])
guards :: Expr' 'Rec -> RecLang
guards e = Filter e (Return Unit)

nest = Nest
