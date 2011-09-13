module Distribution.Desk.Utils where

import Control.Monad (filterM)
import Data.Char (toLower)
import Data.List (intercalate)
import System.Directory
import System.FilePath

die :: String -> IO a
die msg = ioError (userError msg)

lowercase :: String -> String
lowercase = map toLower

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
