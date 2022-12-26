{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant M.pure" #-}
module Test where
import qualified MonadSyntax as M
import CompileQuery


table :: String -> [ExprType] -> RecLang
table s tys = OpLang (HasType (OpLang (Opaque s)) (ListTy $ TupleTyp tys))

userTable :: RecLang
userTable = table "user" [intTy]
barTable :: RecLang
barTable = table "bar" [intTy]
fooTable :: RecLang
fooTable = table "foo" [intTy]
testQ :: RecLang
testQ = M.do
   a <- userTable
   _ <- testQ
   M.return a
  
   
testFlat :: RecLang
testFlat = M.do
   let a = userTable
   _ <- a
   _ <- a
   o <- barTable
   M.pure o

testLeftNest :: RecLang
testLeftNest = M.do
   M.do
       _ <- userTable
       fooTable
   M.pure (nest barTable)

testRightNest :: RecLang
testRightNest = M.do
   a <- userTable
   let
    b = AggrNested SumT $ M.do
       f <- fooTable
       guards (a .== f)
       M.pure (Proj 0 f)
   M.pure (Tuple [a, b])
guards :: Expr' 'Rec -> RecLang
guards e = Filter e (Return Unit)

nest = Nest
