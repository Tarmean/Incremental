{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
module ValueNaming where

import qualified Data.Map.Strict as M
import Data.Functor.Identity
import qualified Data.Set as S
import Util
import qualified Data.Map.Lazy as ML
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer
import CompileQuery
import Rewrites (VarGenT, genVar, withVarGenT, maxVar)
import Data.Data(Data)
import Data.Typeable ((:~:)(Refl), eqT)
import OpenRec
import GHC.Stack

data HashConsEnv
    = HashConsEnv
    { hashCons :: M.Map Expr Var
    , binding :: M.Map Var Expr
    , nameMap :: M.Map Var Var
    } deriving (Eq, Ord, Show, Data)

type M = StateT HashConsEnv (VarGenT Identity)

(!!!) :: (HasCallStack, Ord k, Show k) => M.Map k v -> k -> v
m !!! k = case M.lookup k m of
    Just v -> v
    Nothing -> error $ "Key not found: " ++ show k

tryRewrite :: forall a m. (Applicative m, Data a) => (Expr -> m Expr) -> a -> m a
tryRewrite f a = case eqT @a @Expr of
  Just Refl -> f a
  Nothing -> pure a

childVars :: Expr -> [Var]
childVars = runQ
  (tryQuery_ @Expr \case
    Ref v -> Just [v]
    _ -> Nothing
    ||| recurse)

overExpr :: Expr -> M Expr
overExpr = fmap Ref . hashconsExpression

minExpressions :: Trans M
minExpressions = 
   tryTransM @Lang (\rec -> \case
       OpLang (Let v e b) -> Just $ do
           e' <- rec e
           case e' of
               Ref v' -> do
                   modify \env -> env { nameMap = M.insert v v' (nameMap env) }
                   rec b
               _ -> error "Illegal normalization"
       _ -> Nothing)
   ||| (recurse >>> tryTransM_ @Expr (Just . fmap Ref . hashconsExpressionFlat))

hashconsExpressionFlat :: Expr -> M Var
hashconsExpressionFlat e = do
    case e of
        Ref v -> do
            nm <- gets nameMap
            pure $ M.findWithDefault v v nm
        _ -> do
            hc <- gets hashCons
            case M.lookup e hc of
                Just v -> pure v
                Nothing -> do
                    v <- genVar "v"
                    modify $ \s -> s
                        { hashCons = M.insert e v hc
                        , binding = M.insert v e $ binding s
                        }
                    pure v
hashconsExpression :: Expr -> M Var
hashconsExpression e = do
    e <- gmapM (tryRewrite overExpr ) e
    hashconsExpressionFlat e



topoSort :: M.Map Var Expr -> [Var] -> [Var]
topoSort m vs = execWriter $ evalStateT (mapM_ go vs) mempty
  where
    go x = do
       when (x `S.member` relevant) $ do
           seen <- gets (S.member x)
           unless seen $ do
             modify (S.insert x)
             let doBefore = maybe [] childVars (m M.!? x)
             mapM_ go doBefore
             tell [x]
    relevant = S.fromList vs

-- FIXME for async binds
popForLevel :: M.Map Level [Var] -> HashConsEnv -> Level -> [(Var,Expr)]
popForLevel m env l = case M.lookup l m of
    Nothing -> []
    Just vs -> [(v,t) | v <- topoSort (binding env) vs, Just t <- [translationFor v]]
  where
    translationFor v
      | Just e <- binding env M.!? v = Just e
      | Just v' <- nameMap env M.!? v = Just (Ref v')
      | otherwise = Nothing -- error ("popForLevel: impossible" <> show v)

insertLevels :: M.Map Var Level -> HashConsEnv -> Lang -> Lang
insertLevels levels env = addRoot . runT' (
    recurse >>> 
     tryTrans_ @Lang \case
        Bind h v e -> Just
            let bs = popForLevel revLevels env (levels !!! v)
            in Bind h v $ foldr (\(v',e) b -> OpLang (Let v' e b)) e bs
        AsyncBind ls e -> Just
            let
              (firstVar,_,_) = head ls
              bs = popForLevel revLevels env (levels !!! firstVar)
            in AsyncBind ls $ foldr (\(v',e) b -> OpLang (Let v' e b)) e bs
        _ -> Nothing)
  where
    revLevels = M.fromListWith (<>) $ [(v,[l])|  (l,v) <- M.toList levels, snd v /= l]
    rootLevel = popForLevel revLevels env (0, Var 0 "")
    addRoot :: Lang -> Lang
    addRoot l0 =  foldr (\(v',e) b -> OpLang (Let v' e b)) l0 rootLevel
    -- !_ = error (prettyS $ M.toList revLevels)

doHoistLevels :: TopLevel -> TopLevel
doHoistLevels tl = runIdentity $ withVarGenT (maxVar tl) $ do
    defs' <- flip traverse (defs tl) $ \(args,l) -> do
        l <- hoistLevels l
        pure (args, l)
    pure tl { defs = defs' }
   
   
hoistLevels :: Lang -> VarGenT Identity Lang
hoistLevels l = do
    (l', hcEnv) <- runStateT (runT minExpressions l) (HashConsEnv mempty mempty mempty)
    let baseDepth = depthQuery l'
        bestDepths = computeLevels baseDepth hcEnv
        l'' = insertLevels bestDepths hcEnv l'

    pure l''

type Level = (Int,Var)
-- | Given hashcons mapping and given levels for non-expression vars, compute the max level for each var
computeLevels :: M.Map Var Level -> HashConsEnv -> M.Map Var Level
computeLevels nonExprLevels env = out
  where
     maxChildLevel expr = maximum $ (0,Var 0 "") : [ M.findWithDefault (0,Var 0 "") v' out | v' <- childVars expr ]
     out = nonExprLevels
         <> ML.fromList [ (v, maxChildLevel expr) | (v,expr) <- M.toList (binding env) ]
         <> ML.fromList [(v, out M.! v') | (v,v') <- M.toList (nameMap env)]

-- | Compute at which depth for-loop bound variables come into scope
depthQuery :: Data a => a -> M.Map Var Level
depthQuery a = flip runReader 1 $ runQT (
   tryQueryM @Lang (\rec -> \case
       Bind hd vr bod -> Just $ do
           d <- ask
           b <- local (+1) $ rec bod
           h <- local (+1) $ rec hd
           pure $ M.insert vr (d,vr) (M.union b h)
       AsyncBind ls bod -> Just $ do
           d <- ask
           b <- local (+1) $ rec bod
           let firstVar = (\(v,_,_) -> v) $ head ls
           pure $ M.fromList [(v, (d,firstVar)) | (v,_,_) <- ls] <> b 
       _ -> Nothing)
    ||| recurse) a
