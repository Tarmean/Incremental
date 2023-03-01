-- | Execute a test compiler run
module Example (main) where
import Analysis (optPass)
import CoroutineTransform (doCoroutineTransform)
import Rewrites (nestedToThunks, simpPass, dropInferred, lowerUnpack, compactVars, inlineLets, sinkBinds, lookupToLoop_)
import CompileQuery (toTopLevel, RecLang, TopLevel, pprint, Source, defs)
import qualified Data.Map as M
import Test (testRetNested, testAgg)
import HoistThunks (doLifting)
import Elaborator (elaborate)
-- import UnduplicateGrouping (mergeGroupingOps)
import UnpackStructs (unpackStructs, mergeSlices)
import TypedDSL (coerceLang, DSL)
import DemandAnalysisTransform (dropDeadArgs)
import ValueNaming (doHoistLevels)
import LangToSQL (langToSQL)
import SQL (SQL)
mergeGroupingOps = id

runTest :: DSL [a] -> TopLevel
runTest =  dropInferred . mergeSlices . unpackStructs . elaborate . simpPass . mergeGroupingOps . sinkBinds . inlineLets . compactVars . lowerUnpack . simpPass . dropInferred . doCoroutineTransform . dropDeadArgs . doLifting . elaborate . simpPass . nestedToThunks . optPass . toTopLevel . coerceLang

-- runTest =  simpPass . nestedToThunks . optPass . toTopLevel
-- runTest = simpPass . nestedToThunks . optPass . toTopLevel
--
showTL :: TopLevel -> [(Source, SQL)]
showTL tl = [ (src, langToSQL def) | (src, (_,def)) <- M.toList (defs tl) ]

-- | An example function.
main :: IO ()
main = do
   let rt = runTest testAgg
   pprint rt
   pprint $ showTL rt
