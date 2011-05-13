{-# LANGUAGE DeriveDataTypeable #-}

module Main where

import Foreign.Maude
import System.Console.CmdArgs.Implicit
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)
import Text.Printf (printf)

data SimpleMaude = SimpleMaude
    { fmtStr :: String
    , loads  :: [FilePath]
    } deriving (Eq, Show, Data, Typeable)

simplemaude = SimpleMaude
    { fmtStr = def &= typ "FORMAT" &= opt "%s" &= argPos 0
    , loads  = def &= typ "FILES"  &= args
    } &= help "Perform a Maude rewrite"
      &= summary "simplemaude v0.1.0"

main :: IO ()
main = do
    sm <- cmdArgs simplemaude
    s <- getContents
    let term = printf (fmtStr sm) s
    result <- rewrite (loads sm) term
    case result of
        Just r -> putStrLn (resultTerm r)
        Nothing -> do
            hPutStrLn stderr "Failed to rewrite term"
            exitFailure
