module Main where

import Language.K.Core.Parser

main :: IO ()
main = interact ((++ "\n") . either show id . parseKterm)
