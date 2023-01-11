-- | Execute a test compiler run
module Example (main) where
import Analysis (optPass, analyzeArity)
import CoroutineTransform (doCoroutineTransform)
import Rewrites (nestedToThunks, simpPass, dropInferred, lowerUnpack, compactVars, inlineLets, sinkBinds)
import CompileQuery (toTopLevel, RecLang, TopLevel, pprint)
import Test (testRetNested, testAgg)
import HoistThunks (doLifting)
import Elaborator (elaborate)


-- runTest :: RecLang -> TopLevel
runTest :: RecLang -> TopLevel
runTest =  simpPass . inlineLets . sinkBinds . compactVars . lowerUnpack . simpPass . dropInferred . doCoroutineTransform . doLifting . elaborate . simpPass . nestedToThunks . optPass . toTopLevel
-- runTest =  simpPass . nestedToThunks . optPass . toTopLevel
-- runTest = simpPass . nestedToThunks . optPass . toTopLevel

-- | An example function.
main :: IO ()
main = pprint $ runTest testAgg
