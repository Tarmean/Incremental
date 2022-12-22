-- | An example module.
module Example (main) where
import Analysis (optPass, analyzeArity)
import CoroutineTransform (doCoroutineTransform)
import Rewrites (nestedToThunks, simpPass)
import CompileQuery (toTopLevel, RecLang, TopLevel, pprint)
import Test (testRightNest)
import HoistThunks (doLifting)


-- runTest :: RecLang -> TopLevel
runTest :: RecLang -> TopLevel
runTest = optPass .  simpPass . doCoroutineTransform . doLifting . simpPass . nestedToThunks . optPass . toTopLevel

-- | An example function.
main :: IO ()
main = pprint $ runTest testRightNest
