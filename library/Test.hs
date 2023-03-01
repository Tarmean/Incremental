{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE OverloadedRecordDot #-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant M.pure" #-}
-- | Some test queries
module Test where
import qualified TypedDSL as T
import CompileQuery

table :: String -> [ExprType] -> T.DSL [a]
table s tys = T.ALang $ OpLang (HasType Given (OpLang (Opaque s (TableMeta (FD []) []))) (ListTy RootTy $ tupleTyp tys))

userTable :: T.DSL [(Int, String)]
userTable = table "user" [intTy, stringTy]
barTable :: T.DSL [(Int, Int)]
barTable = table "bar" [intTy, intTy]
fooTable :: T.DSL [(Int, String)]
fooTable = table "foo" [intTy, stringTy]
testQ :: T.DSL [Int]
testQ = T.do
   a <- userTable
   _ <- testQ
   T.return a._1
  
-- testRetNested :: RecLang
testRetNested :: T.DSL [(Int, (Int, Int))]
testRetNested = sec
  where
    first = T.do
       a <- userTable
       T.return (a, barTable)
    sec = T.do
        m <- first
        b <- m._2
        T.return (m._1._1, b)
   
testAgg :: T.DSL [(String, Int)]
testAgg = T.do
    y <- users_in_group "mygroup"
    T.pure (y._2, usage y._1)
  where

    usage user_id = T.sum $ T.do
        a <- jobTable
        T.guard (a._1 T.==. user_id)
        T.return (a._2 * a._3)
    users_in_group group = T.distinct $ T.do
       u <- userTable
       ug <- userGroupsTable
       g <- groupsTable
       T.guard (ug._1 T.==. u._1)
       T.guard (ug._2 T.==. g._2)
       T.guard (group T.==. g._1)
       T.pure u

    jobTable :: T.DSL [(Int, Int, Int, Int)]
    jobTable = table "job" [intTy, intTy, intTy, intTy]
    userGroupsTable :: T.DSL [(Int, Int)]
    userGroupsTable = table "userGroups" [intTy, intTy]
    groupsTable :: T.DSL [(String, Int)]
    groupsTable = table "groups" [stringTy, intTy]

-- -- testFlat :: RecLang
-- -- testFlat = M.do
-- --    let a = userTable
-- --    _ <- a
-- --    _ <- a
-- --    o <- barTable
-- --    M.pure o

-- -- testLeftNest :: RecLang
-- -- testLeftNest = M.do
-- --    M.do
-- --        _ <- userTable
-- --        fooTable
-- --    M.pure (nest barTable)

-- -- testRightNest :: RecLang
-- -- testRightNest = M.do
-- --    a <- userTable
-- --    let
-- --     b = AggrNested SumT $ M.do
-- --        f <- fooTable
-- --        guards (a .== f)
-- --        M.pure (Proj 0 2 f)
-- --    M.pure (Tuple [a, b])
-- -- guards :: Expr' 'Rec -> RecLang
-- -- guards e = Filter e (Return Unit)

-- -- nest = Nest
-- -- iter = OpLang . Call

-- -- -- view :: Expr' 'Rec -> [Expr' 'Rec]
-- -- -- view (Tuple ls) = [Proj i l | (i,l) <- zip [0..] ls]
-- -- -- view a = error ("view: " ++ prettyS (toTopLevel $ Return a))
-- -- fail _ = undefined
