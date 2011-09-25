{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-
This is prototype code. Don't expect much from it.
-}
module KRun.Main where

import Control.Applicative ((<$>))
import Control.Monad (when)
import Data.Char (isSpace)
import Data.Either (rights)
import Data.List (intercalate)
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Foreign.Maude
import Language.K.CellsToXml (cellsToXml')
import Language.K.Core.Parser
import Language.K.Core.Pretty.RaisedMode (prettyPrint)
import System.Console.CmdArgs
import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process
import Text.Printf

import Distribution.Desk.Types
import Distribution.Desk.Utils
import Distribution.Desk.Parser
import KRun.XPath

data KRun = KRun
    { krunSetVars :: [String]
    , krunInFile  :: FilePath
    , krunPgmArgs :: [String]
    } deriving (Eq, Show, Data, Typeable)

kRunInit :: KRun
kRunInit = KRun
    { krunSetVars = def &= explicit &= name "s" &= name "set" &= typ "VAR=str"
      &= help "Set VAR to str in the initial configuration"
    , krunInFile = def &= typFile &= argPos 0
    , krunPgmArgs = def &= typ "PGM_ARGS" &= args
    } &= help "Execute K definitions."
      &= summary "krun v0.2.0"

main :: IO ()
main = do
    krun <- cmdArgs kRunInit
    deskFile <- findDeskFile "."
    desk <- parseDeskFile deskFile
    pgm <- ProgramSource <$> T.readFile (krunInFile krun)
    kast <- flattenProgram desk pgm
    mmr <- evalKastIO desk kast
    when (isNothing mmr) $
        die "Maude failed to produce a result"
    let mr = fromJust mmr
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

-- | Type representing a flattened K term.
newtype Kast = Kast Text
    deriving Show

-- | Type representing uncompiled program source code.
newtype ProgramSource = ProgramSource Text
    deriving Show

-- | Rewrites a flattened K term (Kast) in the compiled K definition.
--evalKast :: Desk -> Kast -> IO (Maybe MaudeResult)
--evalKast desk (Kast k) = rewrite [compiledFile desk] evalTerm
--    where evalTerm = printf "#eval('$PGM(.List{K}) |-> (%s))" (T.unpack k)

-- | Evaluate a term using the Java IO wrapper around Maude.
evalKastIO :: Desk -> Kast -> IO (Maybe MaudeResult)
evalKastIO desk (Kast k) = do
    tmpDir <- getTmpDir
    -- determine files for communicating with the wrapper
    let [cmdFile, outFile, errFile] = map (tmpDir </>) ["maude_in", "maude_out", "maude_err"]

    -- write the file from which the wrapper will read the command to execute
    cmdh <- openFile cmdFile WriteMode
    T.hPutStr cmdh "erew #eval('$PGM(.List{K}) |-> ("
    T.hPutStr cmdh k
    T.hPutStr cmdh ")) ."
    hClose cmdh

    -- run the wrapper
    jar <- getWrapperJar
    let args = javaArgs jar ++ wrapperArgs desk tmpDir cmdFile outFile errFile
    ph <- runProcess "java" args Nothing Nothing Nothing Nothing Nothing
    exitCode <- waitForProcess ph

    -- did the wrapper run correctly?
    exists <- doesFileExist outFile
    when (exitCode /= ExitSuccess || not exists) $
        die $ "Failed to run IO wrapper:\n"
           ++ "java " ++ intercalate " " args

    mmr <- parseMaudeResult <$> T.readFile outFile

    return $ mmr

getWrapperJar :: IO FilePath
getWrapperJar = do
    kbase <- getEnv "K_BASE"
    return $ kbase </> "core" </> "java" </> "wrapperAndServer.jar"

javaArgs :: String -> [String]
javaArgs wrapperJar = ["-jar", wrapperJar]

wrapperArgs :: Desk -> FilePath -> FilePath -> FilePath -> FilePath -> [String]
wrapperArgs desk tmpDir cmdFile outFile errFile =
    [ "--commandFile", cmdFile
    , "--errorFile", errFile
    , "--maudeFile", compiledFile desk
    , "--moduleName", getMainModule desk
    , "--outputFile", outFile
    ]

-- | Flattens a program to a K term.
flattenProgram :: Desk -> ProgramSource -> IO Kast
flattenProgram desk pgm = case getParser desk of
    InternalKast -> runInternalKast desk pgm
    _ -> die "External parser not implemented."

-- | Run the internal parser that turns programs into K terms using
-- the K definition.
runInternalKast :: Desk -> ProgramSource -> IO Kast
runInternalKast desk (ProgramSource pgm) = do
        tmpDir <- getTmpDir
        (tmpFile, tmpHandle) <- openTempFile tmpDir "pgm.in"
        tmpCanonicalFile <- canonicalizePath tmpFile
        T.hPutStr tmpHandle pgm
        hClose tmpHandle
        let kastFile = tmpDir </> (takeBaseName tmpFile <.> ".kast")
        let kastArgs = defaultKastArgs desk tmpCanonicalFile
                    ++ ["-o", kastFile]
        (ih, oh, eh, ph) <- runInteractiveProcess defaultKastCommand kastArgs Nothing Nothing
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

trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

-- Hardcoded defaults:
-- TODO: get rid of these!

distDir :: FilePath
distDir = ".k"

compiledFile :: Desk -> FilePath
compiledFile desk = printf "%s-compiled.maude" (lowercase $ getMainModule desk)

defaultKastCommand :: String
defaultKastCommand = "kast"

defaultKastArgs :: Desk -> FilePath -> [String]
defaultKastArgs desk pgmFile =
    [ "-pgm", pgmFile
    , "-lang", lowercase (getMainModule desk)
    , "-smod", getSyntaxModule desk
    ]
