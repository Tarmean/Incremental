{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BlockArguments #-}
-- | Optimization passes for the query language
module Rewrites where

import CompileQuery
import Control.Monad.Trans
import Control.Monad.Trans.Elevator
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict
import Data.Data
import qualified Data.Set as S
import qualified Data.Map.Lazy as LM
import qualified Data.Map.Strict as M
import OpenRec
import Data.Functor.Identity
import Data.Semigroup (Max(..))
import Data.Coerce (Coercible, coerce)
import Control.Monad.Reader (MonadReader, ReaderT)
import Data.Bifunctor (second)


tagWithFrees :: TopLevel -> TopLevel
tagWithFrees tl = tl { defs = defs' }
  where
    defs' = M.mapWithKey (\k (_args, e) -> (S.toList $ snd (forDefs M.! unSource k), e)) (defs tl)

    forDefs = fixTransitive forDefs0
    forDefs0 :: M.Map Var (S.Set Var, S.Set Var)
    forDefs0 = M.mapWithKey (\k (_args, e) -> escaped k e) $ M.mapKeysMonotonic unSource  (defs tl)
    escaped k e =  second dropBound $ S.partition (\x -> Source x `M.member` defs tl) (freeVarsQ e) 
      where
       dropBound = (S.\\ M.findWithDefault mempty k bound)


    bound = M.map (\(_args, e) -> execWriter $ runT (withBoundT (\a b -> tell a *> b) >>> recurse) e) (M.mapKeysMonotonic unSource  $ defs tl)

    trans1 :: M.Map Var (S.Set Var, S.Set Var) -> M.Map Var (S.Set Var, S.Set Var)
    trans1 m = M.mapWithKey (\k (a,b) -> (a, b <> (concatMapS argsFor a S.\\ boundBy k))) m
      where
        argsFor a = maybe mempty snd (m M.!? a)
        boundBy k = M.findWithDefault mempty k bound
        concatMapS f a = S.unions (S.map f a)
    fixTransitive :: M.Map Var (S.Set Var, S.Set Var) -> M.Map Var (S.Set Var, S.Set Var)
    fixTransitive m = if m == m' then m else fixTransitive m'
      where m' = trans1 m


newtype VarGenT m a = VarGenT { runVarGenT :: StateT Int m a }
  deriving (Functor, Applicative, Monad, MonadTrans)
  deriving (MonadState s) via Elevator (StateT Int) m
  deriving (MonadReader s) via Elevator (StateT Int) m
class Monad m => MonadVar m where
    genVar :: String -> m Var
instance Monad m => MonadVar (VarGenT m) where
    genVar s = VarGenT $ do
        i <- get
        put (i + 1)
        pure (Var i s)
deriving via Elevator (StateT s) m instance MonadVar m => MonadVar (StateT s m) 
deriving via Elevator (WriterT s) m instance (Monoid s, MonadVar m) => MonadVar (WriterT s m) 
deriving via Elevator (ReaderT s) m instance (MonadVar m) => MonadVar (ReaderT s m) 
instance (MonadTrans t, Monad (t m), MonadVar m) => MonadVar (Elevator t m) where
    genVar = lift . genVar
withVarGenT :: Monad m => Int -> VarGenT m a -> m a
withVarGenT i = flip evalStateT i . runVarGenT

withVarGenT' :: Int -> VarGenT m a -> m (a, Int)
withVarGenT' i = flip runStateT i . runVarGenT

-- calcArity :: 


type LiftFuns m = StateT (M.Map Fun ([Local], Lang)) (VarGenT m)

maxVar :: Data a => a -> Int
maxVar = getMax . runQ (
     tryQuery_ (\case
       LRef @'Flat v -> Just $ Max (uniq v)
       _ -> Nothing)
 ||| tryQuery_ (\case
       Ref @'Flat v -> Just $ Max (uniq v)
       _ -> Nothing)
 ||| recurse)



bindGuardT :: Lang -> Maybe Lang
bindGuardT (Bind (Filter g (Return Unit)) _ e ) = Just (Filter g e)
bindGuardT _ = Nothing

bindBindT :: Functor m => Trans1 m -> Lang -> Maybe (m Lang)
bindBindT rec (Bind (Bind e1 v e2) v' e3) = Just $ Bind e1 v <$> rec (Bind e2 v' e3)
bindBindT _ _ = Nothing

bindUnitT :: Lang' t -> Maybe (Lang' t)
bindUnitT (Bind (Return Unit) _ e) = Just e
bindUnitT _ = Nothing

callThunk :: Lang' t -> Maybe (Lang' t)
callThunk (OpLang (Call (AThunk thunk))) = Just (OpLang $ Force thunk)
callThunk _ = Nothing

bindRightUnitT :: Lang' t -> Maybe (Lang' t)
bindRightUnitT (Bind m v (Return (Ref v'))) | v == v' = Just m
bindRightUnitT _ = Nothing

bindLeftUnitT :: Functor m => Trans1 m -> Lang -> Maybe (m Lang)
bindLeftUnitT rec (Bind (Return a) v e) = Just (rec $ subst v a e)
bindLeftUnitT _ _ = Nothing

trivialThunk :: Expr -> Maybe Expr
trivialThunk (AThunk (Thunk (Source s) [])) = Just (Ref s)
trivialThunk _ = Nothing

hoistFilter :: Lang' t -> Maybe (Lang' t)
hoistFilter (Bind (Filter g e) v e') = Just (Filter g (Bind e v e'))
hoistFilter _ = Nothing

trivPack :: Expr -> Maybe Expr
trivPack (Pack [x]) = Just (Ref x)
trivPack _ = Nothing

projTuple :: Expr -> Maybe Expr
projTuple (Proj i _ (Tuple ls)) = Just (ls !! i)
projTuple _ = Nothing


simpPass :: Data a => a -> a
simpPass = runIdentity . runT (
   recurse >>> (langRewrites ||| exprRewrites))
  where
   langRewrites = tryTrans (useFirst [bindGuardT, bindUnitT, bindRightUnitT, callThunk, hoistFilter]) ||| tryTransM bindLeftUnitT ||| tryTransM bindBindT
   exprRewrites = tryTrans $ useFirst [ projTuple ]
   useFirst = ala First mconcat


ala :: forall s m n a0. (Coercible (m s) (n s)) => (m a0 -> n a0) -> ([n s] -> n s) -> [s -> m s] -> s -> m s
ala _cons folder args = coerce out
  where
     args'  = coerce args :: [s -> n s]
     out x = folder (args' <&> x)
     (<&>) fs a= ($ a) <$> fs
    

subst :: Var -> Expr -> Lang -> Lang
subst v sub = runIdentity . runT (
    tryTrans (\case
       (Ref v'::Expr) | v == v' -> Just sub
       _ -> Nothing)
    -- |||
    -- tryTrans (\case
    --    (LRef v'::Lang) | v == v' -> Just sub
    --    _ -> Nothing)
    ||| recurse)

nestedToThunks :: TopLevel -> TopLevel
nestedToThunks tl0 =  tl
  where
    tl = tl0 { defs = M.map (second doTrans) $ defs $ tagWithFrees tl0 }
    doTrans = runIdentity . runT (tryTrans_ nestToThunk ||| tryTrans_ nestToThunkL ||| tryTrans_ dropDumbThunk ||| recurse)

    nestToThunk :: Expr -> Maybe Expr
    nestToThunk (Nest (LRef r)) = Just $ AThunk (Thunk (Source r) (argsOf r))
    nestToThunk (AggrNested op (LRef r)) = Just $ Aggr op (Thunk (Source r) (argsOf r))
    nestToThunk _ = Nothing
    nestToThunkL (LRef r::Lang) 
      | Just args <- tryArgsOf r = Just $ OpLang (Force $ Thunk (Source r) args)
    nestToThunkL _ = Nothing
    dropDumbThunk :: Expr -> Maybe Expr
    dropDumbThunk (AThunk (Thunk (Source a) [])) = Just $ Ref a
    dropDumbThunk _ = Nothing
    argsOf :: Var -> [Var]
    argsOf v = case LM.lookup (Source v) (defs tl) of
      Just ([], _) -> error (prettyS v <> " Did you forgot to run optPass before nestedToThunks?")
      Just (args, _) -> args
      Nothing 
        | otherwise -> error ("Undefined function" <> show v)
    tryArgsOf :: Var -> Maybe [Var]
    tryArgsOf v = case LM.lookup (Source v) (defs tl) of
      Just ([], _) -> Nothing
      Just (args, _) -> Just args
      Nothing 
        | otherwise -> Nothing

dropInferred :: Data a => a -> a
dropInferred = runT' (
  recurse >>>
      tryTrans_ @Lang \case
         (OpLang (HasType Inferred e _)) -> Just e
         _ -> Nothing
  |||
      tryTrans_ @Expr \case
         (HasEType Inferred e _) -> Just e
         _ -> Nothing
  )

dropTopLevel :: TopLevel' p -> TopLevel' p
dropTopLevel a = a { defs = M.map dropDefs (defs a) }
  where
    dropDefs (l,r) = (filter ((`M.notMember` defs a) . Source) l, r)

    -- aggrToFun :: Monad m => Expr -> LiftFuns m Expr
    -- aggrToFun (Aggr op r)
    --     | frees <- S.toList (freeVarsQ r)
    --     , not (null frees) = do
    --        v <- Fun <$> genVar "F"
    --        modify (M.insert v (frees, l))
    --        pure (ThunkArg v AnyType (fmap Ref frees))

    -- hoistFuncs (Thunk f es) = do
    --     (vs, l) <- gets (M.! f)
    --     pure (Call f (zipWith (\v e -> BOp Eql (ValArg e) (ValArg (Ref v))) vs es))

-- inlineReturns :: 
