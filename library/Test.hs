{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE DataKinds #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant M.pure" #-}
-- | Some test queries
module Test where
import qualified MonadSyntax as M
import CompileQuery
import Control.Arrow (Arrow(second))
import Data.Functor.Identity (Identity(..))


table :: String -> [ExprType] -> RecLang
table s tys = OpLang (HasType Given (OpLang (Opaque s)) (ListTy RootTy $ TupleTyp tys))

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
        n <- first
        b <- OpLang $ Union (iter (Proj 1 2 m)) (iter (Proj 1 2 n))
        M.return (Tuple [Proj 0 2 m, b])
   
testAgg :: RecLang
testAgg = Bind (users_in_group (Lit $ StrLit "mygroup")) (Var 0 "y") (Return $ usage (Ref (Var 0 "y")))
  where
    jobTable :: RecLang
    jobTable = table "job" [intTy, intTy, intTy, intTy]
    userGroupsTable :: RecLang
    userGroupsTable = table "userGroups" [intTy, intTy]
    groupsTable :: RecLang
    groupsTable = table "userGroups" [stringTy, intTy]
    usage user_id = AggrNested SumT $ M.do
        a <- jobTable
        guards (Proj 0 4 a .== user_id)
        M.return (BOp Mult (Proj 1 4 a) (Proj 2 4 a) )
    users_in_group group = OpLang $ Distinct $ M.do
       u <- userTable
       ug <- userGroupsTable
       g <- groupsTable
       guards (Proj 0 2 ug .== Proj 0 1 u)
       guards (Proj 1 2 ug .== Proj 1 2 g)
       guards (group .== Proj 0 2 g)
       M.pure (Proj 0 1 u)

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
       M.pure (Proj 0 2 f)
   M.pure (Tuple [a, b])
guards :: Expr' 'Rec -> RecLang
guards e = Filter e (Return Unit)

nest = Nest
iter = OpLang . Call

-- view :: Expr' 'Rec -> [Expr' 'Rec]
-- view (Tuple ls) = [Proj i l | (i,l) <- zip [0..] ls]
-- view a = error ("view: " ++ prettyS (toTopLevel $ Return a))
fail _ = undefined
