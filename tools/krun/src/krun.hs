{-# LANGUAGE DeriveDataTypeable #-}
{-
This is prototype code. Don't expect much from it.
-}
module Main where

import Control.Applicative ((<$>))
import Control.Monad (when)
import Data.List (intercalate)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Foreign.Maude
import System.Console.CmdArgs
import System.Exit
import System.FilePath
import System.Directory
import System.IO
--import System.IO.Temp
import System.Process
import Text.Printf

import Distribution.Desk.Types
import Distribution.Desk.Utils
import Distribution.Desk.Parser

data KRun = KRun
    { krunInFile :: FilePath
    } deriving (Eq, Show, Data, Typeable)

kRunInit :: KRun
kRunInit = KRun
    { krunInFile = def &= typFile &= argPos 0
    } &= help "Execute K definitions."
      &= summary "krun v0.1.0"

main :: IO ()
main = do
    krun <- cmdArgs kRunInit
    deskFile <- findDeskFile "."
    desk <- parseDeskFile deskFile
    pgm <- ProgramSource <$> T.readFile (krunInFile krun)
    kast <- flattenProgram desk pgm
    mmr <- evalKast desk kast
    case mmr of
        Nothing  -> die "Maude failed to produce a result"
        Just res -> putStrLn (resultTerm res)

-- | Type representing a flattened K term.
newtype Kast = Kast Text
    deriving Show

-- | Type representing uncompiled program source code.
newtype ProgramSource = ProgramSource Text
    deriving Show

-- | Rewrites a flattened K term (Kast) in the compiled K definition.
evalKast :: Desk -> Kast -> IO (Maybe MaudeResult)
evalKast desk (Kast k) = rewrite [compiledFile desk] evalTerm
    where evalTerm = printf "#eval('$PGM(.List{K}) |-> (%s))" (T.unpack k)

-- | Flattens a program to a K term.
flattenProgram :: Desk -> ProgramSource -> IO Kast
flattenProgram desk pgm = case getParser desk of
    DefaultKast _ -> runDefaultKast desk pgm
    _ -> die "External parser not implemented."


-- | Run the default internal parser that turns programs into K terms using
-- the K definition.
runDefaultKast :: Desk -> ProgramSource -> IO Kast
runDefaultKast desk (ProgramSource pgm) = do
--    = withTempFile "." "pgm.in" $ \tmpFile tmpHandle -> do
        (tmpFile, tmpHandle) <- openTempFile "." "pgm.in"
        tmpCanonicalFile <- canonicalizePath tmpFile
        T.hPutStr tmpHandle pgm
        hClose tmpHandle
        let kastArgs = defaultKastArgs desk tmpCanonicalFile
        let kastFile = replaceExtension tmpFile ".kast"
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


-- Hardcoded defaults:
-- TODO: get rid of these!

compiledFile :: Desk -> FilePath
compiledFile desk = printf "%s-compiled.maude" (lowercase $ getMainModule desk)

defaultKastCommand :: String
defaultKastCommand = "kast"

defaultKastArgs :: Desk -> FilePath -> [String]
defaultKastArgs desk pgmFile =
    [ "-pgm", pgmFile
    , "-sort", getProgramSort desk
    , "-lang", lowercase (getMainModule desk)
    , "-smod", getSyntaxModule desk
    ]
