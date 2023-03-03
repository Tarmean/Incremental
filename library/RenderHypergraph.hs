{-# OPTIONS -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | Render Graphs [(Node, [Node])] via graphviz
module RenderHypergraph where

import qualified Data.Set as S
import qualified Data.Map.Strict as M
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.GraphViz

import Control.Monad.State
import Control.Monad.Writer.Strict
import Util ( prettyS )
import Prettyprinter (Pretty)
import Debug.Trace (trace, traceM)
import Data.Bifunctor (first)

-- | Render a graph
renderGraph :: Pretty n => Gr (Maybe n) () -> FilePath -> IO ()
renderGraph g fp = void (runGraphviz (graphToDot params g) Svg fp)
  where
    params = nonClusteredParams { fmtNode = \(_,l) -> [toLabel (maybe "<AND>" prettyS l)]
                                , fmtEdge = \(a,b,_) -> [toLabel $ prettyS (a,b)]
                                }

type NId = Int
type M n = StateT (M.Map n NId, NId) (Writer (S.Set (NId, Maybe n), [(NId, NId, ())]))
-- | Turn our format into an fgl graph
-- We add intermediate nodes to represent the hyperedges
toFgl :: forall n. (Pretty n, Ord n) => [(n, [n])] -> Gr (Maybe n) ()
toFgl rules = mkGraph (S.toList nodeSet) edgeSet
  where
    (nodeSet, edgeSet) = execWriter $ flip execStateT (mempty, 0) $ do
       forM_ rules $ \(l, rs) -> do
         case rs of
           [r] -> do
             l <- addNode l
             r <- addNode r
             void $ addEdge r l
           _ -> do
             nid <- genId
             l <- addNode l
             rs <- traverse addNode rs
             addEdge nid l
             forM_ rs $ \r -> addEdge r nid
    nextId :: M n NId
    nextId = do
      (s,i) <- get
      put (s,i + 1)
      return i
    genId = do
      i <- nextId
      tell (S.singleton (i, Nothing), mempty)
      return i
    addNode n = do
      (m, _) <- get
      case m M.!? n of
        Just v -> pure v
        Nothing -> do
          i <- nextId
          modify (first (M.insert n i))
          tell (S.singleton  (i, Just n), mempty)
          return i
    addEdge :: NId -> NId -> M n ()
    addEdge l r  = tell (mempty, [(l,r,())])









