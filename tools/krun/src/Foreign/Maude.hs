{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Foreign.Maude
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- This package provides a simple interface (via the 'rewrite' functions)
-- for doing Maude rewrites from within Haskell.  The following steps are
-- performed every time the 'rewrite' functions are executed: 
--
-- 1. A temporary file is created that contains the necessary commands.
--
-- 2. The temporary file (with any other input files) is executed by Maude.
--
-- 3. The temporary file is removed.
--
-- 4. The output from step 2 is parsed and returned.
--
-- This is a simple way to perform a single rewrite command, but it is
-- inefficient for performing many rewrite commands.  See /Future Work/
-- below.
-----------------------------------------------------------------------------

module Foreign.Maude
    (
    -- * Configuration
      MaudeConf(..)
    , defaultConf

    -- * Invoking Maude
    , MaudeResult(..)
    , SearchResult(..)
    , rewrite
    , rewriteWith

    -- * Parsing Maude's output
    , parseMaudeResult
    , parseSearchResults

    -- * Examples
    -- $examples

    -- * Future Work
    -- $future
    ) where

import Control.Monad (when)
import Data.Char (digitToInt, isSpace)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO (hPutStr, hPutStrLn, hClose, openTempFile)
import System.Directory (getCurrentDirectory, removeFile)
import System.Process (readProcess)
import Text.Parsec
import Text.Parsec.Text

-- | Configuration of Maude's execution.
data MaudeConf = MaudeConf
    { maudeCmd    :: FilePath   -- ^ Path to the Maude executable.
    , loadFiles   :: [FilePath] -- ^ Files to load before running a command.
    , printParens :: Bool       -- ^ Whether Maude should print with parentheses.
    } deriving (Eq, Show)

-- | The default configuration used by the 'rewrite' function.
defaultConf :: MaudeConf
defaultConf = MaudeConf
    { maudeCmd    = "maude"
    , loadFiles   = []
    , printParens = False
    }

-- | Maude option flags which force Maude's output to be as relevant as
-- possible.
maudeArgs :: [String]
maudeArgs =
    [ "-no-banner"
    , "-no-advise"
    , "-no-wrap"
    , "-no-ansi-color"
    ]

-- | The result of a Maude rewrite.
data MaudeResult = MaudeResult
    { resultSort :: Text  -- ^ The sort of the rewritten term.
    , resultTerm :: Text  -- ^ The rewritten term.
    , statistics :: Text  -- ^ Statistics printed by Maude.
    } deriving (Show)

-- | The result of a Maude search.
data SearchResult = SearchResult
    { searchResultState :: Integer
    , searchStatistics :: Text
    , searchResultTerm :: Text
    } deriving (Show)

-- | @rewrite files term@ performs a single Maude rewrite command on
-- @term@ using the 'defaultConf' configuration loaded with @files@.
rewrite :: [FilePath] -> Text -> IO (Maybe MaudeResult)
rewrite files term = rewriteWith defaultConf{ loadFiles = files } term

-- | @rewriteWith conf term@ performs a single Maude rewrite command on
-- @term@ using the configuration @conf@.
rewriteWith :: MaudeConf -> Text -> IO (Maybe MaudeResult)
rewriteWith conf term = do
    runner <- newRunnerFile conf term
    let args = maudeArgs ++ [runner]
    out <- readProcess (maudeCmd conf) args []
    removeFile runner
    return $ parseMaudeResult (T.pack out)

-- | Parse Maude's output into a MaudeResult.  The current implementation
-- does very little sanity checking and can not parse Maude failures.
parseMaudeResult :: Text -> Maybe MaudeResult
parseMaudeResult txt =
    case parse pMaudeResult "" txt of
        Left _ -> Nothing
        Right r -> Just r


parseSearchResults :: Text -> Maybe [SearchResult]
parseSearchResults txt =
    case parse pSearchResults "" txt of
        Left _ -> Nothing
        Right r -> Just r

-- | Parsec parser that parses the output of a successful Maude
-- rewrite command.
pMaudeResult :: Parser MaudeResult
pMaudeResult = do
    optional (string "Maude>")
    spaces
    stats <- pLine
    string "result"
    spaces
    sort <- many1 (satisfy (/= ':'))
    char ':'
    spaces
    lines <- many1 pLine
    let term = T.concat . filter (/= "Bye.") $ lines
    return $ MaudeResult
        { resultSort = T.pack sort
        , resultTerm = term
        , statistics = stats
        }

-- | Parsec parser that parses the output of a successful Maude
-- search command.
pSearchResults :: Parser [SearchResult]
pSearchResults = do
    optional (string "Maude>" >> spaces)
    pSearchResult `endBy1` newline

-- | Parsec parser that parses a single search result.
pSearchResult :: Parser SearchResult
pSearchResult = do
    symbol "Solution"
    integer
    spaces
    state <- parens (symbol "state" >> integer)
    newline
    stats <- pLine
    var <- pLine
    lines <- many1 pLine
    let term = T.concat lines
    return $ SearchResult
        { searchResultState = state
        , searchStatistics = stats
        , searchResultTerm = term
        }

-- | Parse a single line.
pLine :: Parser Text
pLine = do
    x <- many1 (satisfy (/= '\n'))
    newline
    return $ T.pack x

-- | Create a temporary file which contains the commands Maude should run at
-- startup: load file commands, formatting commands, the rewrite command,
-- and the quit command.
newRunnerFile :: MaudeConf -> Text -> IO FilePath
newRunnerFile conf term = do
    currDir <- getCurrentDirectory
    (tmpf, tmph) <- openTempFile currDir "runner.maude"
    mapM_ (\f -> T.hPutStr tmph "load " >> hPutStrLn tmph f) (loadFiles conf)
    when (printParens conf) $
        T.hPutStrLn tmph "set print with parentheses on ."
    T.hPutStrLn tmph "set show command off ."
    T.hPutStr tmph "rewrite "
    T.hPutStr tmph term
    T.hPutStrLn tmph " ."
    T.hPutStrLn tmph "quit"
    hClose tmph
    return tmpf

-- | Remove leading and trailing whitespace from a string.
trim :: Text -> Text
trim = f . f
    where f = T.reverse . T.dropWhile isSpace

-- Lexers:

integer = number 10 digit

parens = between (char '(') (char ')')

symbol s = do { x <- string s; spaces; return x }

-- copied from Parsec:
number base baseDigit
    = do { digits <- many1 baseDigit
         ; let n = foldl (\x d -> base * x + toInteger (digitToInt d)) 0 digits
         ; seq n (return n)
         }

{- $examples

Maude's standard prelude is loaded by default, even when no input files are
specified:

>>> rewrite [] "not (A:Bool or B:Bool) implies (not A:Bool) and (not B:Bool)"
Just (MaudeResult
    { resultSort = "Bool"
    , resultTerm = "true"
    , statistics = "rewrites: 13 in 0ms cpu (0ms real) (~ rewrites/second)"
    })

The name of the module in which to reduce a term can be given explicitly:

>>> rewrite [] "in NAT-LIST : reverse(1 2 3 4)"
Just (MaudeResult
    { resultSort = "NeNatList"
    , resultTerm = "4 3 2 1"
    , statistics = "rewrites: 6 in 0ms cpu (0ms real) (~ rewrites/second)"
    })

Using a naive implementation of primes in Maude:

>>> rewrite ["primes.maude"] "2 .. 20"
Just (MaudeResult
    { resultSort = "PrimeSet"
    , resultTerm = "2 3 5 7 11 13 17 19"
    , statistics = "rewrites: 185 in 0ms cpu (0ms real) (~ rewrites/second)"
    })

If we are only interested in the statistics:

>>> liftM statistics <$> rewrite ["primes.maude"] "2 .. 1000"
Just "rewrites: 409905 in 839ms cpu (856ms real) (488014 rewrites/second)"
-}

{- $future

This Maude interface is very minimal first step.  It could be extended in the
following ways:

* Better handling of Maude failures.  Failure messages should be parsed and
  returned to the user.

* Support for other Maude commands besides @rewrite@. 

* A Maude monad that handles failure and multiple Maude commands efficiently
  is a long-term goal for this package.

* Consider taking of advantage of Maude's -xml-log option.
-}
