# [Incremental][]

Experimental compiler to turn nested Haskell into Datalog or SQL.


The core idea is similar to Database-Supported Haskell (DSH) but the formalism is quite different. Rather than generating numpy-like pointfree code, Incremental uses some standard compiler techniques.


Haskell queries can contain nested containers, grouping, higher order functions, etc:

```Haskell

usage :: Expr UserId -> Expr Int
usage user_id = memo $ S.sum $ S.do
    j <- S.iter jobs
    S.wheres (j.user_id S.== u.user_id)
    S.pure (j.runtime * j.cpus)

highest_usage :: Expr [User] -> Expr [User]
highest_usage = S.take 10 . S.sortBy (usage . user_id)

users_in_group :: Expr String -> Expr [User]
users_in_group group = S.do
    u <- S.iter users
    S.exists $ S.do
       ug <- S.iter userGroups
       g <- S.iter groups
       S.wheres (ug.user S..== u.user_id S.&& ug.group S.== g.group_id S.&& g.group_name == group)
    S.pure u


out = highest_usage (users_in_group "foo")
```

This compiles into a series of flat common table expressions (CTE's)  without lateral joins:

```SQL
WITH
  T1 AS (SELECT DISTINCT U.user_id f0
         FROM Users U, UserGroups UG, groups G
         WHERE U.user_id = UG.user AND UG.group = G.group_id)
  T2 AS (SELECT U.user_id f0, SUM(j.runtime * j.cpus) f1
         FROM T1, Jobs J
         WHERE T1.f0 = J.user_id
         GROUP BY T1.f0)
SELECT U.*
FROM T2, Users U
WHERE T2.f0 = U.user_id
ORDER BY T2.f1
LIMIT 10
```

Currently, the compiler is pretty bare-bones, and clearly does too much de-lateralization. Even that often beats hand-written queries with lateral joins, though.


The name is from step two of the plan: Compiling (mutually) recursive haskell queries. SQL is not powerful enough for that, so either we'd need a datalog backend or something like pl/pgsql, though
