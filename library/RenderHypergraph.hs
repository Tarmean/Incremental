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
import Data.Bifunctor (first)

-- | Render a graph
renderGraph :: (Pretty lab, Pretty n) => Gr (Either lab n) (Maybe lab) -> FilePath -> IO ()
renderGraph g fp = void (runGraphviz (graphToDot params g) Svg fp)
  where
    params = nonClusteredParams { fmtNode = \(_,l) -> [toLabel (either prettyS prettyS l)]
                                , fmtEdge = \(_,_,lab) -> [toLabel $ prettyS lab]
                                }

type NId = Int
type M n lbl = StateT (M.Map n NId, NId) (Writer (S.Set (NId, Either lbl n), [(NId, NId, Maybe lbl)]))
-- | Turn our format into an fgl graph
-- We add intermediate nodes to represent the hyperedges
toFgl :: forall n lbl. (Ord lbl, Pretty n, Ord n) => [(n, [n], lbl)] -> Gr (Either lbl n) (Maybe lbl) 
toFgl rules = mkGraph (S.toList nodeSet) edgeSet
  where
    (nodeSet, edgeSet) = execWriter $ flip execStateT (mempty, 0) $ do
       forM_ rules $ \(l, rs, lbl) -> do
         case rs of
           [r] -> do
             l <- addNode l
             r <- addNode r
             void $ addEdge r l (Just lbl)
           _ -> do
             nid <- genId lbl
             l <- addNode l
             rs <- traverse addNode rs
             addEdge nid l Nothing
             forM_ rs $ \r -> addEdge r nid Nothing
    nextId :: M n lbl NId
    nextId = do
      (s,i) <- get
      put (s,i + 1)
      return i
    genId lab = do
      i <- nextId
      tell (S.singleton (i, Left lab), mempty)
      return i
    addNode n = do
      (m, _) <- get
      case m M.!? n of
        Just v -> pure v
        Nothing -> do
          i <- nextId
          modify (first (M.insert n i))
          tell (S.singleton  (i, Right n), mempty)
          return i
    addEdge :: NId -> NId -> Maybe lbl -> M n lbl ()
    addEdge l r  lbl = tell (mempty, [(l,r,lbl)])









