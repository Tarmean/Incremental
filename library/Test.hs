{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant M.pure" #-}
module Test where
import qualified MonadSyntax as M
import CompileQuery
import Control.Arrow (Arrow(second))
import Data.Functor.Identity (Identity(..))


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
  
testRetNested :: RecLang
testRetNested = sec
  where
    first = M.do
       a <- userTable
       M.return (Tuple [a, nest $ M.do
            b <- barTable
            guards (a .== b)
            M.return b])
    sec = M.do
        m <- first
        b <- OpLang $ Union (iter (Proj 1 m)) (iter (Proj 1 m))
        M.return (Tuple [Proj 0 m, b])
   
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
iter = OpLang . Call

-- view :: Expr' 'Rec -> [Expr' 'Rec]
-- view (Tuple ls) = [Proj i l | (i,l) <- zip [0..] ls]
-- view a = error ("view: " ++ prettyS (toTopLevel $ Return a))
fail _ = undefined
