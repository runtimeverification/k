-- Simple XPath CLI utility.
module Main where

import Control.Monad (when)
import System.Environment
import System.Exit
import Text.XML.HXT.Core hiding (when)
import Text.XML.HXT.XPath

main :: IO ()
main = do
    args <- getArgs

    when (null args) $ do
        putStrLn "One argument required (the xpath query)."
        exitFailure

    let query = head args

    rs <- runX $
        readDocument [] ""
        >>>
        getXPathTrees query
        >>>
        -- Is this the best thing to do?
        xshow this

    mapM_ putStrLn rs
