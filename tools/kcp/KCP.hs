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
--   * Use a template file instead of having to specify loads and includes
--     on the command-line.
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
    { load     :: [String]  -- ^ Files to load in the generated K module
    , include  :: [String]  -- ^ Modules to include in the generated K module
    , sort     :: String    -- ^ Sort the program should belong to
    , language :: String    -- ^ Name of the language the program is written in
    , infile   :: FilePath  -- ^ File containing the program to compile
    } deriving (Eq, Show, Data, Typeable)

kcpinit :: KCP
kcpinit = KCP
    { load = ["-compiled"] &= typ "FILE [+]" &= help "Files to load in the generated K module"
    , include = [] &= typ "MODULE [+]" &= help "Modules to include in the generated K module"
    , sort = "Pgm" &= typ "SORT" &= help "Sort the program should belong to (default is Pgm)"
    , language = def &= typ "LANGUAGE" &= argPos 0
    , infile = def &= typFile &= argPos 1
    } &= help "Compile a program into its K Core representation."
      &= summary "kcp v0.1.0"
      &= details (["[+] marked options can be specified multiple times"] ++ detailedHelp)

main :: IO ()
main = do
    kcp' <- cmdArgs kcpinit
    let kcp = completeKCP kcp'

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
    let w  = hPutStr   h
    let wl = hPutStrLn h 
    mapM_ (wl . ("load " ++)) (load kcp)
    wl "kmod KCP-GENERATED is"
    when (not . null $ include kcp) $ do
        w "  including "
        wl . intercalate " + " $ include kcp
    w "  syntax " >> w (sort kcp) >> wl " ::= pgm"
    pgm <- readFile (infile kcp)
    w "  macro pgm = " >> wl pgm
    wl "endkm"
    hClose h
    return f

compileKModule :: KCP -> FilePath -> IO (FilePath, FilePath)
compileKModule kcp kmodf = do
    let cmd = printf cmdfmt kmodf (language kcp)
    h <- runCommand cmd
    waitForProcess h
    exists <- doesFileExist cmodf
    when (not exists) $ do
        hPutStrLn stderr "Error running kcompile-program.sh; see generated outputs."
        exitWith (ExitFailure 2)
    return (mmodf, cmodf)
    where cmdfmt = "kcompile-program.sh %s %s KCP-GENERATED pgm > /dev/null"
          mmodf = replaceExtension kmodf ".maude"
          cmodf = "pgm-compiled.maude"

getCompiledPgm :: String -> Maybe String
getCompiledPgm = liftM snd
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

-- | Expand "-foo" loads/includes into "LANGUAGE-foo" and ensure they are
-- properly capitalized.
completeKCP :: KCP -> KCP
completeKCP kcp = kcp
    { language = language'
    , load = map (map toLower . expand) (load kcp)
    , include = map (map toUpper . expand) (include kcp)
    } where
        language' = map toUpper (language kcp)
        expand r@('-':rs) = language' ++ r
        expand r = r

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
