module MonadSyntax where


import CompileQuery


import Prelude hiding (pure, return, (>>=), (>>))

pure :: Expr' RecLang -> RecLang
pure = return
return :: Expr' RecLang -> RecLang
return = RecLang . Return
(>>=) :: RecLang -> (Expr' RecLang -> RecLang) -> RecLang
(>>=)  = Bound
(>>) :: RecLang -> RecLang -> RecLang
(>>) a b = a >>= const b

-- (>>) :: Lang -> Lang -> Lang
-- (>>) = (>>=) . const
