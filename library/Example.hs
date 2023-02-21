-- | Execute a test compiler run
module Example (main) where
import Analysis (optPass)
import CoroutineTransform (doCoroutineTransform)
import Rewrites (nestedToThunks, simpPass, dropInferred, lowerUnpack, compactVars, inlineLets, sinkBinds, lookupToLoop_)
import CompileQuery (toTopLevel, RecLang, TopLevel, pprint)
import Test (testRetNested, testAgg)
import HoistThunks (doLifting)
import Elaborator (elaborate)
import UnduplicateGrouping (mergeGroupingOps)
import UnpackStructs (unpackStructs, mergeSlices)
import TypedDSL (coerceLang, DSL)
import DemandAnalysisTransform (dropDeadArgs)
import ValueNaming (doHoistLevels)


runTest :: DSL [a] -> TopLevel
-- runTest =  dropInferred . mergeSlices . unpackStructs . elaborate . simpPass . mergeGroupingOps . sinkBinds . inlineLets . compactVars . lowerUnpack . simpPass . dropInferred . doCoroutineTransform . dropDeadArgs . doLifting . elaborate . simpPass . nestedToThunks . optPass . toTopLevel . coerceLang
runTest =  dropInferred . mergeSlices . unpackStructs . elaborate . simpPass . mergeGroupingOps . sinkBinds . inlineLets . compactVars . lowerUnpack . simpPass . dropInferred . doCoroutineTransform . doHoistLevels . dropDeadArgs . doLifting . elaborate . simpPass . nestedToThunks . optPass . toTopLevel . coerceLang

-- runTest =  simpPass . nestedToThunks . optPass . toTopLevel
-- runTest = simpPass . nestedToThunks . optPass . toTopLevel

-- | An example function.
main :: IO ()
main = pprint $ runTest testAgg
