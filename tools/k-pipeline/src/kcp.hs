{-# LANGUAGE DeriveDataTypeable, PatternGuards #-}
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
--   * Support compilation of several programs at the same time.
--   * Print detailed help separately from usage message.
-----------------------------------------------------------------------------

module Main where

import Control.Concurrent
import Data.List
import Data.Char
import System.Console.CmdArgs
import System.Environment
import System.Exit
import System.IO
import System.IO.Error
import System.Process
import Text.Printf

data KCP = KCP
    { kcpTemplate :: FilePath  -- ^ File containing the KCP template
    , kcpLanguage :: String    -- ^ Name of the language the program is written in
    , kcpInfile   :: FilePath  -- ^ File containing the program to compile
    } deriving (Eq, Show, Data, Typeable)

kcpinit :: KCP
kcpinit = KCP
    { kcpTemplate = "kcp_template.maude" &= typFile &= explicit &= name "t" &= name "template"
    , kcpLanguage = def &= typ "LANGUAGE" &= argPos 0
    , kcpInfile = def &= typFile &= argPos 1
    } &= help "Compile a program into its K Core representation."
      &= summary "kcp v0.2.0"

data KCPError = PgmNotFound
              | UnexpectedEOF
              | MaudeError
    deriving (Eq, Show)

errMsg :: KCPError -> String
errMsg PgmNotFound = "Could not find 'pgm in the generated Maude module."
errMsg UnexpectedEOF = "Got unexpected EOF trying to read Maude's output."
errMsg MaudeError = "Maude reported a warning or an error."

main :: IO ()
main = do
    kcp <- cmdArgs kcpinit
    kBase <- getKBase
    let compileDir = kBase ++ "/core/maude/compiler/"
    r <- kcompilePgm kcp compileDir

    case r of
        Right s -> do
            putStrLn s
            exitSuccess
        Left (e, eout) -> do
            errln $ "Fatal KCP error: " ++ errMsg e
            if null eout
                then errln "There are no Maude error messages to report."
                else do
                    errln "Maude errors:"
                    mapM_ errln eout
            exitFailure

-- | Get the $K_BASE environment variable or exit if the variable is not found.
getKBase :: IO String
getKBase = catch (getEnv "K_BASE")
    (\e -> if isDoesNotExistError e
        then do
            errln "Fatal: Please set the K_BASE environment variable."
            exitFailure 
        else ioError e)

-- | Run Maude to compile the input program.
kcompilePgm :: KCP -> FilePath -> IO (Either (KCPError, [String]) String)
kcompilePgm kcp compileDir = do
    -- Read in the template file and input file. 
    template <- readFile (kcpTemplate kcp)
    pgm <- readFile (kcpInfile kcp)
    
    -- Combine the template and the program to form the program module that
    -- will be compiled.
    let pgmmod = printf template pgm

    -- Start Maude.
    (ih, oh, eh, ph) <- runInteractiveProcess "maude" maudeArgs Nothing Nothing
    hSetBinaryMode ih False
    hSetBinaryMode oh False

    -- rmv will hold a Result
    rmv <- newEmptyMVar

    -- Start the stdout reader thread.
    otid <- forkIO $ outputReader oh rmv

    -- emv will hold any lines Maude prints to stderr.
    emv <- newEmptyMVar

    -- Start the stderr reader thread.
    etid <- forkIO $ errorReader eh emv rmv

    -- Write the commands that will compile the program to Maude's stdin.
    let w s = hPutStrLn ih s
    w pgmmod
    w "set include PL-BOOL off ."
    w "set include BOOL on ."
    let loadc m = w $ "load " ++ compileDir ++  m
    mapM_ loadc [ "prelude-extras"
                , "meta-k"
                , "printing"
                , "compile-program-interface"
                ]
    w "loop compile-program ."
    w $ printf "(compileProgram %s KCP pgm .)" (kcpLanguage kcp)
    w "quit"
    hFlush ih
    hClose ih

    -- Wait for the result.
    r <- takeMVar rmv

    -- Clean up.
    hClose oh
    hClose eh

    -- Add Maude's stderr output to the Left component.
    case r of
        Right s -> return $ Right s
        Left  e -> do
            eout <- takeMVar emv
            return $ Left (e, eout)

-- Convenient type synonym used by the types of 'outputReader' and
-- 'errorReader'.
type Result = Either KCPError String

-- | Consume Maude's stdout looking for the compiled program.
outputReader :: Handle -> MVar Result -> IO ()
outputReader oh rmv =
    catch (handleln =<< hGetLine oh)
          (\e -> if isEOFError e
                   then putMVar rmv $ Left UnexpectedEOF
                   else ioError e)
    where
        handleln l
            | l == endMarker
            = putMVar rmv $ Left PgmNotFound

            | Just (rhs, lhs) <- parseEq l
            , "'pgm" `isInfixOf` rhs
            = putMVar rmv $ Right lhs

            | otherwise = outputReader oh rmv

        endMarker = "---K-MAUDE-GENERATED-OUTPUT-END-----"

-- | Consume Maude's stderr. If Maude ever writes to stderr, kcp gracefully
-- fails.
errorReader :: Handle -> MVar [String] -> MVar Result -> IO ()
errorReader eh emv rmv = do
    e <- hGetLines eh
    putMVar emv e
    putMVar rmv $ Left MaudeError

-- | Parse a Maude equation line into its left-hand side and right-hand side.
--
-- >>> parseEq "eq foo=bar ."
-- Just ("foo", "bar")
parseEq :: String -> Maybe (String, String)
parseEq s = clean . break (== '=') =<< stripPrefix "eq " s
    where clean (l, '=':r) = Just (l, trim $ init r)
          clean _ = Nothing

-- | Convenient alias for writing to stderr.
errln :: String -> IO ()
errln = hPutStrLn stderr

-- | Read several lines from the given 'Handle'.
hGetLines :: Handle -> IO [String]
hGetLines h = do
    eof <- hIsEOF h
    if not eof
        then do
            l <- hGetLine h
            ls <- hGetLines h
            return (l:ls)
        else return []

-- | Remove leading and trailing whitespace from a string.
trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

-- | Arguments passed to Maude to make its output as relevant as possible.
maudeArgs :: [String]
maudeArgs =
    [ "-no-banner"
    , "-no-advise"
    , "-no-wrap"
    , "-no-ansi-color"
    ]

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
