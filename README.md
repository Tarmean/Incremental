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

## Related

DSH and the ferry compiler are the obvious (and pretty much only) prior approaches. Unfortunately, they mirrored Data Parallel Haskell in both approach (the "flattening transformation") and destiny: Very complex implementations, no longer supported, and unusable with current compiler versions. The new technique here hopefully does the same transformations, should yield even better SQL, and require  *much* less code to implement.

A related experiment is HaskellORM, which uses a less expressive query language but offers automatic updates. Here, we view the query as an in-memory view of the DB.
The core type in HaskellORM is not query or ORM specific, so automatic updates should be workable for Incremental (assuming the queries fulfills some simple fundep constraints) https://github.com/Tarmean/HaskellORM/blob/master/library/Classes.hs#L713

## Approach:


The compiler works by translating queries into a simple language. We translate nested queries into calls to top-level functions, explicitely passing arguments.

Using a slightly simplified version of the above example:


```javascript
    let v_1 = for y_0 in Distinct for l_4 in #user :: [(Int,)] {
                             for l_8 in #userGroups :: [(Int, Int)] {
                                 for l_12 in #userGroups :: [([Char], Int)] {
                                     when (l_8.0 == l_4.0) when (l_8.1 == l_12.1) when ("mygroup" == l_12.0) yield l_4.0
                                   }
                               }
                           } {
            yield SUM(v_29(y_0))
          }
        v_29 = \y_0 -> for l_30 in #job :: [(Int, Int, Int, Int)] {
            when (l_30.0 == y_0) yield l_30.1 * l_30.2
          }
    in
    v_1
```

Function calls are either turned into lazy thunks (structs which hold the variables), or async calls when we actually want to use the result:

```javascript
    let v_1 = for y_0 in Distinct for l_4 in #user :: [(Int,)] {
                             for l_8 in #userGroups :: [(Int, Int)] {
                                 for l_12 in #userGroups :: [([Char], Int)] {
                                     when (l_8.0 == l_4.0) when (l_8.1 == l_12.1) when ("mygroup" == l_12.0) yield l_4.0
                                   }
                               }
                           } {
            async { SUM t_30 = v_29(y_0) } yield t_30
          }
        v_29 = \y_0 -> for l_30 in #job :: [(Int, Int, Int, Int)] {
            when (l_30.0 == y_0) yield l_30.1 * l_30.2
          }
    in
    v_1
```

Then we can turn async calls into

- insertions into a request table
- plus joins to a result table

The `call` is then an intermediate query which transforms all requests into all results in one pass. This performs memoization and can improve query performance over random accessing.

```javascript
let v_1 = for l_31 in *stash_30 {
        let (y_0,) = *l_31 in let t_30 := v_SumT_29 [[y_0]] in yield t_30
      }
    v_29 = for p_33 in *stash_30 {
        for l_35 in Distinct let (u_34,) = *p_33 in yield (u_34,) {
            let (y_0,) = *l_35
            in for l_30 in #job :: [(Int, Int, Int, Int)] {
                when (l_30.0 == y_0) yield ((y_0), l_30.1 * l_30.2)
              }
          }
      }
    v_SumT_29 = group(SUM) *v_29
    stash_30 = for y_0 in Distinct for l_4 in #user :: [(Int,)] {
                              for l_8 in #userGroups :: [(Int, Int)] {
                                  for l_12 in #userGroups :: [([Char], Int)] {
                                      when (l_8.0 == l_4.0) when (l_8.1 == l_12.1) when ("mygroup" == l_12.0) yield l_4.0
                                    }
                                }
                            } {
        yield (y_0)
      }
in
v_1
```
