module Main where

import Language.K.CellsToXml
import Data.ByteString.Char8
import Prelude hiding (interact)

main :: IO ()
main = interact (either error id . cellsToXml')
