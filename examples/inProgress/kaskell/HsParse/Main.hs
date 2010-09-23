{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) David Lazar and Michael Ilseman, 2010
-- License     :  BSD3
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- HsParse is a small command-line utility for parsing Haskell and displaying
-- the AST in different formats.
-----------------------------------------------------------------------------

module Main where

import Data.Generics
import Data.Tree

import Language.Haskell.Exts
import System.Console.CmdArgs

-- | Ways of displaying the AST. 
data OutputMode
    = Standard    -- ^ using the standard @show@ instance
    | PrettyTree  -- ^ as a 2-dimensional tree, for easy viewing
    | Maude       -- ^ in a way parseable by Maude
    deriving (Eq, Show, Data, Typeable)

-- | Show a module according to the given @OutputMode@.
showModule :: OutputMode -> Module -> String
showModule Standard   = show
showModule PrettyTree = showAsTree
showModule Maude      = gshow

-- | Show @Data@ as a nice 2-dimentional tree.
showAsTree :: (Data a) => a -> String
showAsTree = drawTree . data2tree

-- | Represent @Data@ as @Tree@ (copied from Astview and SYB 2, sec. 3.4).
data2tree :: Data a => a -> Tree String
data2tree = gdefault `extQ` atString
    where
        atString x = Node x [] -- don't traverse strings
        gdefault x = Node (showConstr $ toConstr x) (gmapQ data2tree x)

-- | Command-line options; used by @CmdArgs@.
data HsParse = HsParse
    { outputMode :: OutputMode
    , inputFile  :: FilePath
    } deriving (Eq, Show, Data, Typeable)

-- | @CmdArgs@ configuration.
hsparse :: HsParse
hsparse = HsParse
    { outputMode = Maude &= typ "MODE" &= help "Set the output mode"
    , inputFile  = def   &= typFile    &= argPos 0
    } &= help "A command-line utility for parsing Haskell"
      &= summary "hsparse v0.0.1"

-- | Entry point for the utility.
main :: IO ()
main = do
    HsParse mode file <- cmdArgs hsparse
    hsmodule <- parseFile file
    case hsmodule of
        ParseOk r -> putStrLn (showModule mode r)
        ParseFailed loc err -> error ("Parse error: " ++ err)
