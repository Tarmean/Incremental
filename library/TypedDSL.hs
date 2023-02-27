{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module TypedDSL where
import CompileQuery
import Data.String (IsString (fromString))
import GHC.TypeLits (type (-), Nat, ErrorMessage (..), TypeError)
import GHC.Types(RuntimeRep(..), TYPE, Constraint, Type)
import GHC.Records



data DSL a = ALang (Lang' 'Rec) | AnExpr (Expr' 'Rec)


instance IsString (DSL String) where
    fromString = AnExpr . Lit . StrLit

instance IsString (DSL Int) where
    fromString = AnExpr . Lit . IntLit . read

instance Num (DSL Int) where
    fromInteger i = AnExpr $ Lit $ IntLit $ fromInteger i
    (*) = binOp Mult
    (-) = error "unimplemented"
    (+) = error "unimplemented"
    abs = error "unimplemented"
    signum = error "unimplemented"

type family AssertNotList a err :: Constraint where
  AssertNotList [Char] _ = ()
  AssertNotList [a] err = err 
  AssertNotList a err = ()

distinct :: DSL [a] -> DSL [a]
distinct = ALang . OpLang . Distinct . coerceLang

sum :: DSL [Int] -> DSL Int
sum = AnExpr . AggrNested SumT . coerceLang
type family DropDSL a where
    DropDSL (DSL a) = a
    DropDSL [a] = [DropDSL a]
    DropDSL (a, b) = (DropDSL a, DropDSL b)
    DropDSL (a, b,c) = (DropDSL a, DropDSL b, DropDSL c)
    DropDSL (a,b,c,d) = (DropDSL a, DropDSL b, DropDSL c, DropDSL c)
    DropDSL a = a

type family NoDSL a err :: Constraint where
    NoDSL (DSL a) _err = TypeError ('Text "DSL not allowed in this position: " ':<>: 'ShowType a)
    NoDSL [a] err = NoDSL a err
    NoDSL (a, b) err = (NoDSL a err, NoDSL b err)
    NoDSL (a, b,c) err = (NoDSL a err, NoDSL b err, NoDSL c err)
    NoDSL (a,b,c,d) err = (NoDSL a err, NoDSL b err, NoDSL c err, NoDSL c err)
    NoDSL a _err = ()

type family ThrowError (a::Type) :: Type where
    ThrowError () = TypeError ('Text "Could not infer types to inject values. Maybe add more type annotations?")
    ThrowError a = a
type HasNoDSL (a) = NoDSL a (ThrowError ())
    

class Inj a where
  inj :: a -> DSL (DropDSL a)
instance (HasNoDSL a) => Inj (DSL a) where
  inj = id
instance  Inj String where
  inj = fromString
instance (Inj a, Inj b) => Inj (a, b) where
  inj (a, b) = AnExpr $ tuple [coerceExpr $ inj a, coerceExpr $ inj b]
instance (Inj a, Inj b, Inj c) => Inj (a, b, c) where
  inj (a, b, c) = AnExpr $ tuple [coerceExpr $ inj a, coerceExpr $ inj b, coerceExpr (inj c)]
instance (Inj a, Inj b, Inj c, Inj d) => Inj (a, b, c, d) where
  inj (a, b, c, d) = AnExpr $ tuple [coerceExpr $ inj a, coerceExpr $ inj b, coerceExpr (inj c), coerceExpr (inj d)]

coerceExpr :: DSL b -> Expr' 'Rec
coerceExpr (AnExpr e) = e
coerceExpr (ALang l) = Nest l

coerceLang :: DSL b -> Lang' 'Rec
coerceLang (ALang l) = l
coerceLang (AnExpr e) = OpLang (Call e)

-- instance (Inj a) => Inj [a] where
--   inj = foldR (lBOp Union) . map inj


dslReturn :: DSL a -> DSL [a]
dslReturn (AnExpr a) = ALang $ Return a
dslReturn (ALang a) = ALang $ Return $ Nest a
dslBind :: DSL [a] -> (DSL a -> DSL [b]) -> DSL [b]
dslBind a f = ALang $ FBind (coerceLang a) (coerceLang . f . AnExpr)


pure,return :: Inj a => a -> DSL [DropDSL a]
return = dslReturn . inj
pure = dslReturn . inj
(>>=) :: DSL [a] -> (DSL a -> DSL [b]) -> DSL [b]
(>>=) = dslBind
(>>) :: DSL [a] -> DSL [b] -> DSL [b]
(>>) m f = dslBind m (const f)


union :: DSL [a] -> DSL [a] -> DSL [a]
union a b = ALang $ OpLang $ Union (coerceLang a) (coerceLang b)


class NotList a
instance (AssertNotList a (TypeError ('Text "List type not allowed here"))) => NotList a
(==.) :: (NotList a) => DSL a -> DSL a -> DSL Bool
(==.) (AnExpr l) (AnExpr r) = AnExpr (BOp Eql l r)
(==.) _ _ = error "Type error"

guard :: DSL Bool -> DSL [()]
guard (AnExpr b) = ALang $ Filter b (Return Unit)
guard _ = error "Type error"


binOp :: BOp -> DSL Int -> DSL Int -> DSL Int
binOp bop (AnExpr l) (AnExpr r) = AnExpr (BOp bop l r)
binOp _ _ _ = error "type error"

instance (c ~ a) => HasField "_1" (DSL (a,b)) (DSL c) where
   getField (AnExpr a) = AnExpr (Proj 0 2 a)
   getField _ = error "Type error"
instance (c ~ b) => HasField "_2" (DSL (a,b)) (DSL c) where
   getField (AnExpr a) = AnExpr (Proj 1 2 a)
   getField _ = error "Type error"
instance HasField "_1" (DSL (a,b,c)) (DSL a) where
   getField (AnExpr a) = AnExpr (Proj 0 3 a)
   getField _ = error "Type error"
instance HasField "_2" (DSL (a,b,c)) (DSL b) where
   getField (AnExpr a) = AnExpr (Proj 1 3 a)
   getField _ = error "Type error"
instance HasField "_3" (DSL (a,b,c)) (DSL c) where
   getField (AnExpr a) = AnExpr (Proj 2 3 a)
   getField _ = error "Type error"

instance HasField "_1" (DSL (a,b,c,d)) (DSL a) where
   getField (AnExpr a) = AnExpr (Proj 0 4 a)
   getField _ = error "Type error"
instance HasField "_2" (DSL (a,b,c,d)) (DSL b) where
   getField (AnExpr a) = AnExpr (Proj 1 4 a)
   getField _ = error "Type error"
instance HasField "_3" (DSL (a,b,c,d)) (DSL c) where
   getField (AnExpr a) = AnExpr (Proj 2 4 a)
   getField _ = error "Type error"
instance HasField "_4" (DSL (a,b,c,d)) (DSL d) where
   getField (AnExpr a) = AnExpr (Proj 3 4 a)
   getField _ = error "Type error"
