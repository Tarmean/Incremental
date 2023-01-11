module Util where
import Prettyprinter
import Prettyprinter.Render.String (renderString)

prettyS :: Pretty a => a -> String
prettyS = renderString . layoutPretty defaultLayoutOptions . pretty

pprint :: Pretty a => a -> IO ()
pprint = putStrLn . prettyS


