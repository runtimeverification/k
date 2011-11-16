module KRun.Utils where

import Control.Monad (filterM)
import Data.Char (isSpace, toLower)
import Data.List (intercalate)
import System.Directory
import System.FilePath
import System.IO (hPutStrLn, stderr)
import System.Exit (exitFailure)

die :: String -> IO a
--die msg = ioError (userError msg)
die msg = do
    hPutStrLn stderr "Error:"
    hPutStrLn stderr msg
    exitFailure

lowercase :: String -> String
lowercase = map toLower

trim :: String -> String
trim = f . f
    where f = reverse . dropWhile isSpace

-- Code copied from Cabal.
findDeskFile :: FilePath -> IO FilePath
findDeskFile dir = do
    deskFiles <- getFilesWithExt ".desk" dir
    case deskFiles of
        []         -> noDesk
        [deskFile] -> return deskFile
        multiple   -> multiDesk multiple

    where noDesk = die $ "No desk file found.\n"
                      ++ "Please create a K description file <name>.desk"
          
          multiDesk l = die $ "Multiple desk files found.\n"
                           ++ "Please use only one of: "
                           ++ intercalate " " (map show l)

findDeskFile' :: FilePath -> IO (Maybe FilePath)
findDeskFile' dir = do
    deskFiles <- getFilesWithExt ".desk" dir
    case deskFiles of
        []         -> return Nothing
        [deskFile] -> return $ Just deskFile
        multiple   -> multiDesk multiple

    where multiDesk l = die $ "Multiple desk files found.\n"
                           ++ "Please use only one of: "
                           ++ intercalate " " (map show l)

-- Code copied from Cabal.
getFilesWithExt :: String -> FilePath -> IO [FilePath]
getFilesWithExt extension dir = do
    files <- getDirectoryContents dir
    filterM doesFileExist
        [ dir </> file
        | file <- files
        , let (name, ext) = splitExtension file
        , not (null name) && ext == extension
        ]
