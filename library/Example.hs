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


-- runTest :: RecLang -> TopLevel

runTest :: DSL [a] -> TopLevel
runTest =  elaborate . simpPass . nestedToThunks . optPass . toTopLevel . coerceLang
-- runTest =  elaborate . dropInferred . mergeSlices . unpackStructs . elaborate . simpPass . mergeGroupingOps . inlineLets . sinkBinds . compactVars . lowerUnpack . simpPass . dropInferred . doCoroutineTransform . doLifting . elaborate . simpPass . nestedToThunks . optPass . toTopLevel . coerceLang

-- runTest =  simpPass . nestedToThunks . optPass . toTopLevel
-- runTest = simpPass . nestedToThunks . optPass . toTopLevel

-- | An example function.
main :: IO ()
main = pprint $ runTest testAgg
