-- | Execute a test compiler run
module Example (main) where
import Analysis (optPass, analyzeArity)
import CoroutineTransform (doCoroutineTransform)
import Rewrites (nestedToThunks, simpPass, dropInferred)
import CompileQuery (toTopLevel, RecLang, TopLevel, pprint)
import Test (testRetNested)
import HoistThunks (doLifting)
import Elaborator (elaborate)


-- runTest :: RecLang -> TopLevel
runTest :: RecLang -> TopLevel
runTest =  simpPass . dropInferred . doCoroutineTransform . doLifting . simpPass . elaborate . nestedToThunks . optPass . toTopLevel
-- runTest = simpPass . nestedToThunks . optPass . toTopLevel

-- | An example function.
main :: IO ()
main = pprint $ runTest testRetNested
