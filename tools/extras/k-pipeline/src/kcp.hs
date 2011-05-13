{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Main
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Compile a program into its K Core representation.
--
-- TODO:
--   * Use kompile.pl's program compilation instead of kcompile-program.sh.
--   * Support compilation of several programs at the same time.
--   * Reproduce the functionality of kcompile-program.sh directly in this
--     executable.
--   * Print detailed help separately from usage message.
-----------------------------------------------------------------------------

module Main where

import Control.Monad
import Data.List hiding (sort)
import Data.Maybe
import Data.Char
import System.Console.CmdArgs
import System.Directory
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.Printf

data KCP = KCP
    { kcpTemplate :: FilePath  -- ^ File containing the KCP template
    , kcpLanguage :: String    -- ^ Name of the language the program is written in
    , kcpInfile   :: FilePath  -- ^ File containing the program to compile
    } deriving (Eq, Show, Data, Typeable)

kcpinit :: KCP
kcpinit = KCP
    { kcpTemplate = "kcp_template.k" &= typFile &= explicit &= name "t" &= name "template"
    , kcpLanguage = def &= typ "LANGUAGE" &= argPos 0
    , kcpInfile = def &= typFile &= argPos 1
    } &= help "Compile a program into its K Core representation."
      &= summary "kcp v0.1.0"

main :: IO ()
main = do
    kcp <- cmdArgs kcpinit

    kmodf <- generateKModule kcp
    (mmodf, cmodf) <- compileKModule kcp kmodf
    mmod <- readFile cmodf

    case getCompiledPgm mmod of
        Just pgm -> putStrLn pgm
        Nothing -> do
            hPutStrLn stderr "Error parsing the compiled maude file."
            exitWith (ExitFailure 3)

    removeFile kmodf
    removeFile mmodf
    removeFile cmodf

generateKModule :: KCP -> IO FilePath
generateKModule kcp = do
    currDir <- getCurrentDirectory
    (f, h) <- openTempFile currDir "pgm.k"
    template <- readFile (kcpTemplate kcp)
    pgm <- readFile (kcpInfile kcp)
    let kmod = printf template pgm
    hPutStrLn h kmod
    hClose h
    return f

compileKModule :: KCP -> FilePath -> IO (FilePath, FilePath)
compileKModule kcp kmodf = do
    let cmd = printf cmdfmt kmodf (map toUpper $ kcpLanguage kcp)
    h <- runCommand cmd
    waitForProcess h
    exists <- doesFileExist cmodf
    when (not exists) $ do
        hPutStrLn stderr "Error running kcompile-program.sh; see generated outputs."
        exitWith (ExitFailure 2)
    return (mmodf, cmodf)
    where cmdfmt = "kcompile-program.sh %s %s KCP pgm > /dev/null"
          mmodf = replaceExtension kmodf ".maude"
          cmodf = "pgm-compiled.maude"

getCompiledPgm :: String -> Maybe String
getCompiledPgm = liftM (dropWhile isSpace . snd)
               . listToMaybe
               . filter (isInfixOf "'pgm" . fst)
               . mapMaybe parseEq
               . lines

-- | Parse a Maude equation line into its left-hand side and right-hand side.
--
-- >>> parseEq "eq foo=bar ."
-- Just ("foo", "bar")
parseEq :: String -> Maybe (String, String)
parseEq s = clean . break (== '=') =<< stripPrefix "eq " s
    where clean (l, '=':r) = Just (l, init r)
          clean _ = Nothing

{-
TODO: rewrite the help message to explain the new template-based usage.
detailedHelp =
    [ ""
    , "kcp is a frontend to kcompile-program.sh. It generates a K module"
    , "containing the program specified by FILE which is then compiled by"
    , "kcompile-program.sh. If all is successful, kcp prints the K core"
    , "representation of FILE."
    , ""
    , "For --load and --include, \"-foo\" is the same as LANGUAGE-foo."
    , "LANGUAGE-compiled is loaded by default in the generated K module."
    , ""
    , "Example:"
    , ""
    , "  kcp --load -syntax --include -syntax --sort Exp system-F fib.sf"
    , ""
    , "generates a K module that loads system-F-compiled and system-F-syntax,"
    , "includes system-F-syntax, and has the program in fib.sf as a macro"
    , "subsorted to Exp. This K module is then compiled by kcompile-program.sh"
    ]
-}
