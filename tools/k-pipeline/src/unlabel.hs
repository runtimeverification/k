module Main where

import Language.K.Core.Parser
import Language.K.Core.Pretty.RaisedMode

main :: IO ()
main = interact ((++ "\n") . either show prettyPrint . parseK)
