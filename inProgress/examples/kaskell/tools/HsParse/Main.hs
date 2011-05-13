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

import Data.Char (ord)
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
showModule Maude      = maudeShow

{-
NOTE: The Maude-specific show case below will eventually be a separate module.
It is included here temporarily. 
-}

-- | Maude @show@, based on 'maudeShows'.
maudeShow :: (Data a) => a -> String
maudeShow x = maudeShows x ""

-- | Maude @shows@, using generics.
maudeShows :: (Data a) => a -> ShowS
maudeShows = defaultShows
    `extQ` (shows     :: String  -> ShowS) 
    `extQ` (shows     :: Int     -> ShowS)
    `extQ` (shows     :: Integer -> ShowS)
    `extQ` charShows

-- | Special case for 'Char' to be displayed as an integer.
charShows :: Char -> ShowS
charShows = shows . ord

-- | This is a prefix-show using surrounding \'(\' and \')\', where we recurse into
-- subterms with 'gmapQ'.  This is basically 'gshows' without the special cases.
defaultShows :: (Data a) => a -> ShowS
defaultShows t =
      showChar '('
    . (showString . showConstr . toConstr $ t)
    . (foldr (.) id . gmapQ ((showChar ' ' .) . maudeShows) $ t)
    . showChar ')'

-- | Show @Data@ as a nice 2-dimensional tree.
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
      &= details ["See the Haddock documentation for help on different modes."]

-- | Entry point for the utility.
main :: IO ()
main = do
    HsParse mode file <- cmdArgs hsparse
    hsmodule <- parseFile file
    case hsmodule of
        ParseOk r -> putStrLn (showModule mode r)
        ParseFailed loc err -> error ("Parse error: " ++ err)
