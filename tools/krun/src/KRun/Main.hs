{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ViewPatterns #-}
{-
This is prototype code. Don't expect much from it.
-}
module Main where

import Control.Applicative ((<$>))
import Control.Monad (when)
import Data.Char (isSpace)
import Data.Either (rights)
import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Foreign.Maude
import Language.K.CellsToXml (cellsToXml')
import Language.K.Core.NewParser
import Language.K.Core.NewPretty
import System.Console.CmdArgs
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
import KRun.XPath

main :: IO ()
main = do
    argv <- getArgs
    (argConfig, nonOpts) <- parseOpts argv

    let (groups, maybePgmFile, pgmExt) =
          case nonOpts of
            [] -> ([], Nothing, Nothing)
            _  -> let file = last nonOpts
                  in (init nonOpts, Just file, listToMaybe . takeExtension $ file)
                    where listToMaybe [] = Nothing
                          listToMaybe xs = Just xs
    
    deskFile <- case Map.lookup "desk-file" argConfig of
        Just (File f) -> return $ Just f
        Nothing -> findDeskFile' "."

    config <- mkConfig pgmExt deskFile groups argConfig

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
        
    Bool search <- getVal config "search"
    let kmap = if search then Map.fromList [("noIO", Kast "wlist_(#noIO)(.List{K})")] else Map.empty
    --kmap <- case parseKeyVals $ map T.pack (krunSetVars krun) of
    --    Left err -> die $ "Unable to parse initial configuration value: " ++ err
    --    Right kmap -> return kmap

    File compiledDef <- getVal config "compiled-def"
    existsCompiled <- doesFileExist compiledDef
    when (not existsCompiled) $
        die $ "Could not find compiled definition: " ++ compiledDef
           ++ "\nPlease compile the definition by using `make' or `kompile'."

    pgm <- ProgramSource <$> T.readFile pgmFile
    kast <- flattenProgram config pgm
    maybeMaudeResult <- evalKastIO config (Map.insert "PGM" kast kmap)
    when (isNothing maybeMaudeResult) $
        die "Maude failed to produce a result"
    let maudeResult = fromJust maybeMaudeResult

    File rawMaudeOut <- getVal config "raw-maude-out"
    T.writeFile rawMaudeOut (resultTerm maudeResult `T.append` "\n")

    File prettyMaudeOut <- getVal config "pretty-maude-out"
    if prettyMaudeOut /= "/dev/null"
        then do
            case parse kBag "" (T.unpack $ resultTerm maudeResult) of
                Left err -> do
                    putStrLn "Failed to parse result term!"
                    putStrLn "Attempted to parse:"
                    T.putStrLn (resultTerm maudeResult)
                    putStrLn "Got error(s):"
                    print err
                Right bag -> printDoc $ ppKBag bag
        else return ()

    Bool printStats <- getVal config "statistics"
    when printStats $ do
        -- TODO: make color optional. green:
        T.putStrLn (T.concat ["\ESC[92m", statistics maudeResult, "\ESC[0m"])

{-
    case getOutputMode desk of
        IOServer -> return ()
        Maude -> T.putStrLn (resultTerm mr)
        PrettyPrint -> case cellsToXml' (resultTerm mr) of
            Left err -> die $ "Failed to convert Maude output to XML: " ++ err
            Right xmltext -> do
                let kterms = xpath (getCellQuery desk) (T.unpack xmltext)
                -- TODO: do "trim" in cellsToXml, if possible
                let terms = rights (map (parseK . trim) kterms)
                when (null terms) $
                    die $ "Unable to parse strings resulting from cell query as K terms."
                mapM_ (putStrLn . prettyPrint) terms
-}

-- | Rewrites a flattened K term (Kast) in the compiled K definition.
--evalKast :: Desk -> Kast -> IO (Maybe MaudeResult)
--evalKast desk (Kast k) = rewrite [compiledFile desk] evalTerm
--    where evalTerm = printf "#eval('$PGM(.List{K}) |-> (%s))" (T.unpack k)

-- | Evaluate a term using the Java IO wrapper around Maude.
evalKastIO :: Config -> Map Text Kast -> IO (Maybe MaudeResult)
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

    mmr <- parseMaudeResult <$> T.readFile outFile

    return $ mmr

constructMaudeCmd :: Config -> Map Text Kast -> Text
constructMaudeCmd config kmap = T.pack cmd <> " " <> eval <> " " <> T.pack pat <> " ."
    where String cmd = config ! "maude-cmd"
          eval = (\t -> "#eval(__(" <> t <> ",(.).Map))")
               . T.intercalate ","
               $ Map.foldrWithKey (\k (Kast v) ts ->
               "(_|->_(('$" <> k <> "(.List{K})) , (" <> v <> ")))" : ts) [] kmap
          pat = if search then searchPattern else ""
              where Bool search = config ! "search"
                    String searchPattern = config ! "search-pattern"
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
    ] ++ if io then [] else ["--noServer"]
    where File compiled  = config ! "compiled-def"
          String mainMod = config ! "main-module"
          Bool io = config ! "io"

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
    let kastFile = tmpDir </> (takeBaseName tmpFile <.> ".kast")
    let kastArgs = defaultKastArgs config tmpCanonicalFile
                ++ ["-o", kastFile]
    kastExecutable <- getKastExecutable
    (ih, oh, eh, ph) <- runInteractiveProcess kastExecutable kastArgs Nothing Nothing
    exitCode <- waitForProcess ph
    exists <- doesFileExist kastFile
    when (exitCode /= ExitSuccess || not exists) $
        die $ "Failed to run kast command:\n"
           ++ "kast " ++ intercalate " " kastArgs
    kast <- T.readFile kastFile
    removeFile kastFile
    removeFile tmpFile
    return (Kast kast)

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
    [ "-pgm", pgmFile
    , "-lang", lowercase mainMod
    , "-smod", syntaxMod
    ] where String mainMod = config ! "main-module"
            String syntaxMod = config ! "syntax-module"
