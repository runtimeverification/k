{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns #-}
{-
This is prototype code. Don't expect much from it.
-}
module Main where

import Control.Applicative ((<$>))
import Control.Monad (forM_, when)
import Data.Char (isSpace)
import Data.Either (rights)
import Data.List ((\\), intercalate, isInfixOf)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Foreign.Maude
import Language.K.Core.NewParser
import Language.K.Core.NewPretty
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.Printf
import Text.Parsec (parse)

import Data.Configuration
import Distribution.Desk.Utils
import KRun.InitialValueParser
import KRun.Types
--import KRun.XPath

main :: IO ()
main = do
    argv <- getArgs
    (argConfig, nonOpts, unrecOpts) <- parseOpts argv

    let unrecOpts' = map (dropWhile (== '-')) unrecOpts
    let initVals = filter (elem '=') unrecOpts' 
    let groups = unrecOpts' \\ initVals
    let maybePgmFile = listToMaybe nonOpts

    deskFile <- case Map.lookup "desk-file" argConfig of
        Just (File f) -> return $ Just f
        Nothing -> findDeskFile' "."

    config <- mkConfig deskFile groups argConfig

    Bool printHelp <- getVal config "print-help"
    when (printHelp) $ do
        putStrLn detailedHelp
        exitSuccess

    Bool printVersion <- getVal config "print-version"
    when (printVersion) $ do
        putStrLn versionStr
        exitSuccess

    when (isNothing maybePgmFile) $ do
        usageError ["missing required <file> argument\n"]
    let pgmFile = fromJust $ maybePgmFile

    when (Map.notMember "compiled-def" config) $
        die $ "Could not find a compiled K definition."

    File compiledDef <- getVal config "compiled-def"
    existsCompiled <- doesFileExist compiledDef
    when (not existsCompiled) $
        die $ "Could not find compiled definition: " ++ compiledDef
           ++ "\nPlease compile the definition by using `make' or `kompile'."

    Bool io <- getVal config "io"
    kmap <- case parseKeyVals $ map T.pack initVals of
        Left err -> die $ "Unable to parse initial configuration value: " ++ err
        Right kmap -> return $ kmap `Map.union`
            if io then Map.empty else Map.fromList [("noIO", Kast "wlist_(#noIO)(.List{K})")]

    pgm <- ProgramSource <$> T.readFile pgmFile
    kast <- flattenProgram config pgm
    let kmap' = Map.insert "PGM" kast kmap

    Bool search <- getVal config "do-search"
    if search
        then searchExecution config kmap'
        else standardExecution config kmap'


searchExecution :: Config -> Map Text Kast -> IO ()
searchExecution config kmap = do
    isterm <- hIsTerminalDevice stdin
    kmap' <- case isterm of
        False -> do
            input <- T.getContents
            let stdbuf = Kast $ T.concat ["(# \"", T.replace "\n" "\\n" input, "\"(.List{K}))"]
            return $ Map.insert "stdin" stdbuf kmap
        True -> return kmap
    (_, outFile, errFile) <- evalKastIO config kmap'
    out <- T.readFile outFile
    let maybeSearchResults = parseSearchResults out
    when (isNothing maybeSearchResults) $ do
        putStrLn "Unable to parse Maude's search results:\n"
        T.putStrLn out
        exitFailure
    let searchResults = fromJust maybeSearchResults
    T.putStrLn "Search results:"
    forM_ (zip [1..] searchResults) $ \(i, sr) -> do
        putStrLn $ "\n\ESC[94mSolution " ++ show i ++ ", state " ++ show (searchResultState sr) ++ ":\ESC[0m"
        printResult config (searchResultTerm sr)
        printStatistics config (searchStatistics sr)


standardExecution :: Config -> Map Text Kast -> IO ()
standardExecution config kmap = do
    (_, outFile, errFile) <- evalKastIO config kmap
    out <- T.readFile outFile
    let maybeMaudeResult = parseMaudeResult out
    when (isNothing maybeMaudeResult) $ do
        putStrLn "Unable to parse Maude's output:\n"
        T.putStrLn out
        exitFailure
    let maudeResult = fromJust maybeMaudeResult
    printResult config (resultTerm maudeResult)
    printStatistics config (statistics maudeResult)


printResult :: Config -> Text -> IO ()
printResult config result = do
    String outputMode <- getVal config "output-mode"
    case outputMode of
        "none" -> return ()
        "raw" -> T.putStrLn result
        "pretty" -> do
            case parse kBag "" (T.unpack result) of
                Left err -> do
                    putStrLn "Warning: unable to parse/pretty-print result term:"
                    T.putStrLn result
                    putStrLn "(NB: This may not be your fault. Pretty-printing is an experimental feature.)"
                Right bag -> printDoc $ ppKBag bag
        s -> die $ "Invalid output-mode setting: " ++ s

printStatistics :: Config -> Text -> IO ()
printStatistics config stats = do
    Bool printStats <- getVal config "statistics"
    when printStats $ do
        T.putStrLn (T.concat ["\ESC[94m", stats, "\ESC[0m"])

-- | Evaluate a term using the Java IO wrapper around Maude.
evalKastIO :: Config -> Map Text Kast -> IO (FilePath, FilePath, FilePath)
evalKastIO config kmap = do
    tmpDir <- getTmpDir
    -- determine files for communicating with the wrapper
    let [cmdFile, outFile, errFile] = map (tmpDir </>) ["maude_in", "maude_out", "maude_err"]

    -- write the file from which the wrapper will read the command to execute
    cmdh <- openFile cmdFile WriteMode
    let cmd = constructMaudeCmd config kmap
    T.hPutStrLn cmdh "set show command off ."
    T.hPutStrLn cmdh cmd
    T.hPutStrLn cmdh "quit"
    hClose cmdh

    -- run the wrapper
    jar <- getWrapperJar
    let args = javaArgs jar ++ wrapperArgs config tmpDir cmdFile outFile errFile
    ph <- runProcess "java" args Nothing Nothing Nothing Nothing Nothing
    exitCode <- waitForProcess ph

    -- did the wrapper run correctly?
    exists <- doesFileExist outFile
    when (exitCode /= ExitSuccess || not exists) $
        die $ "Failed to run IO wrapper:\n"
           ++ "java " ++ intercalate " " args

    return (cmdFile, outFile, errFile)

constructMaudeCmd :: Config -> Map Text Kast -> Text
constructMaudeCmd config kmap = T.pack cmd <> " " <> eval <> " " <> T.pack pat <> " ."
    where String cmd = config ! "maude-cmd"
          eval = (\t -> "#eval(__(" <> t <> ",(.).Map))")
               . T.intercalate ","
               $ Map.foldrWithKey (\k (Kast v) ts ->
               "(_|->_((# \"$" <> k <> "\"(.List{K})) , (" <> v <> ")))" : ts) [] kmap
          pat = if search then searchPattern else ""
              where Bool search = config ! "do-search"
                    String searchPattern = config ! "xsearch-pattern"
          (<>) = T.append

getWrapperJar :: IO FilePath
getWrapperJar = do
    kbase <- getEnv "K_BASE"
    return $ kbase </> "core" </> "java" </> "wrapperAndServer.jar"

javaArgs :: String -> [String]
javaArgs wrapperJar = ["-jar", wrapperJar]

wrapperArgs :: Config -> FilePath -> FilePath -> FilePath -> FilePath -> [String]
wrapperArgs config tmpDir cmdFile outFile errFile =
    [ "--commandFile", cmdFile
    , "--errorFile", errFile
    , "--maudeFile", compiled
    , "--moduleName", mainMod
    , "--outputFile", outFile
    ] ++ (if io then [] else ["--noServer"])
      ++ (if log then ["--createLogs"] else [])
    where File compiled  = config ! "compiled-def"
          String mainMod = config ! "main-module"
          Bool io = config ! "io"
          Bool log = config ! "log-io"

-- | Flattens a program to a K term.
flattenProgram :: Config -> ProgramSource -> IO Kast
flattenProgram config pgm = case config ! "parser" of
    String "kast" -> runInternalKast config pgm
    _ -> die "External parser not implemented."

-- | Run the internal parser that turns programs into K terms using
-- the K definition.
runInternalKast :: Config -> ProgramSource -> IO Kast
runInternalKast config (ProgramSource pgm) = do
    tmpDir <- getTmpDir
    (tmpFile, tmpHandle) <- openTempFile tmpDir "pgm.in"
    tmpCanonicalFile <- canonicalizePath tmpFile
    T.hPutStr tmpHandle pgm
    hClose tmpHandle
    let kastArgs = defaultKastArgs config tmpCanonicalFile
    kastExecutable <- getKastExecutable
    (exitCode, kastStdout, kastStderr) <- readProcessWithExitCode kastExecutable kastArgs ""
    when (not (null kastStderr)) $ do
        hPutStrLn stderr "Warning: kast reported errors or warnings:"
        hPutStrLn stderr kastStderr
    when (exitCode /= ExitSuccess) $ do
        die $ "Fatal: kast returned a non-zero exit code: " ++ show exitCode
           ++ "\nAttempted command:\n"
           ++ "kast " ++ intercalate " " kastArgs
    let kast = Kast (T.pack kastStdout)
    removeFile tmpFile
    return kast

getTmpDir :: IO FilePath
getTmpDir = do
    cwd <- getCurrentDirectory
    let tmpDir = cwd </> distDir </> "krun_tmp"
    createDirectoryIfMissing True tmpDir
    return tmpDir

getKastExecutable :: IO FilePath
getKastExecutable = do
    kbase <- getEnv "K_BASE"
    return $ kbase </> "core" </> "kast"

trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

-- Hardcoded defaults:
-- TODO: get rid of these!

distDir :: FilePath
distDir = ".k"

defaultKastArgs :: Config -> FilePath -> [String]
defaultKastArgs config pgmFile =
    [ "--k-definition", kDef
    , "--main-module", mainMod
    , "--syntax-module", syntaxMod
    , pgmFile
    ] where File kDef = config ! "k-definition"
            String mainMod = config ! "main-module"
            String syntaxMod = config ! "syntax-module"
