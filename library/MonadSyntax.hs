{-# LANGUAGE DataKinds #-}
-- | Definitions for -XQualifiedDo
module MonadSyntax where


import CompileQuery


import Prelude hiding (pure, return, (>>=), (>>))

pure :: Expr' 'Rec -> RecLang
pure = return
return :: Expr' 'Rec -> RecLang
return = Return
(>>=) :: RecLang -> (Expr' 'Rec -> RecLang) -> RecLang
(>>=)  = FBind
(>>) :: RecLang -> RecLang -> RecLang
(>>) a b = a >>= const b

-- (>>) :: Lang -> Lang -> Lang
-- (>>) = (>>=) . const
