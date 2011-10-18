{-# LANGUAGE DeriveDataTypeable #-}
module Data.Configuration where

import Control.Applicative ((<$>))
import Control.Arrow (first, second)
import Control.Exception
import Control.Monad (forM, join)
import Data.Char (toUpper)
import Data.List (partition)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Object as Y
import qualified Data.Object.Yaml as Y
import Data.Typeable
import Prelude hiding (catch)
import System.Console.GetOpt
import System.Exit
import System.FilePath

type Config = Map String Value

data Value
    = Bool Bool
    | String String
    | Number Integer
    | File FilePath
    deriving (Eq, Show)

data ValueType
    = BoolType
    | StringType
    | NumberType
    | FileType
    deriving (Eq, Show)

data Setting = Setting
    { settingName :: String
    , settingType :: ValueType
    , settingDesc :: String
    } deriving (Show)

data ConfigException
    = InvalidKeyValue String String ValueType
    | GroupNotFound (Map String Config) String
    | GroupsWithoutDesk [String]
    | KeyNotFound String Config
    deriving (Show, Typeable)

instance Exception ConfigException

readValue :: ValueType -> String -> Maybe Value
readValue BoolType "true" = Just $ Bool True
readValue BoolType "false" = Just $ Bool False
readValue StringType s = Just $ String s
readValue NumberType s = Just $ Number (read s)
readValue FileType s = Just $ File s
readValue _ _ = Nothing

tryReadValue :: String -> String -> IO (String, Value)
tryReadValue k vs = case readValue t vs of
    Just v -> return (k, v)
    Nothing -> throwIO $ InvalidKeyValue k vs t
    where t = getType k

getVal :: Config -> String -> IO Value
getVal config key = case Map.lookup key config of
    Just val -> return val
    Nothing -> throwIO $ KeyNotFound key config

infixl 9 !

(!) :: Config -> String -> Value
config ! key = case Map.lookup key config of
    Just val -> val
    Nothing -> error $ "key " ++ key ++ " not in config."

metadataSettings :: [Setting]
metadataSettings =
    [ Setting "name" StringType "Name of the definition"
    , Setting "version" StringType "Version of the definition"
    , Setting "synopsis" StringType "One-line description of the definition"
    , Setting "license" StringType "License"
    , Setting "authors" StringType "Who created the definition"
    , Setting "maintainer" StringType "Who maintains the definition"
    , Setting "tags" StringType "Comma-separated words describing the definition"
    ]

generalSettings :: [Setting]
generalSettings =
    [ Setting "print-help" BoolType "Display the detailed help message and quit"
    , Setting "print-version" BoolType "Display the version number and quit"
    , Setting "desk-file" FileType "Set Desk file path, instead of searching for it"
    ]

commonKSettings :: [Setting]
commonKSettings =
    [ Setting "main-module" StringType "Name of the main module the program should execute in"
    , Setting "syntax-module" StringType "Name of the syntax module"
    , Setting "search" BoolType "Search for all possible results"
    , Setting "io" BoolType "Use real IO when running the definition"
    , Setting "statistics" BoolType "Print Maude's rewrite statistics"
    ]

advancedKSettings :: [Setting]
advancedKSettings =
    [ Setting "compiled-def" FileType "Path to the compiled K definition"
    , Setting "maude-cmd" StringType "Maude command used to execute the definition (search, erewrite, search, ...)"
    , Setting "search-pattern" StringType "Search pattern"
    , Setting "raw-maude-out" FileType "Where to write the unmodified result term"
    ]

-- TODO: resolve defaults
defaultConfig :: Maybe String -> Config
defaultConfig mExt = Map.fromList $
    [ ("print-help", Bool False)
    , ("print-version", Bool False)
    , ("parser", String "kast")
    , ("maude-cmd", String "erewrite")
    , ("search", Bool False)
    , ("search-pattern", String "=>! B:Bag")
    , ("io", Bool True)
    , ("raw-maude-out", File "/dev/stdout")
    , ("statistics", Bool False)
    ]
    ++ maybe [] (\ext' -> let ext = dropWhile (== '.') ext' in
         [ ("main-module", String $ map toUpper ext)
         , ("syntax-module", String $ map toUpper ext ++ "-SYNTAX")
         , ("compiled-def", File $ ext ++ "-compiled.maude")
         ]) mExt

allSettings :: [Setting]
allSettings = metadataSettings ++ generalSettings ++ commonKSettings ++ advancedKSettings

typeMap :: Map String ValueType
typeMap = Map.fromList $ map (\s -> (settingName s,  settingType s)) allSettings

getType :: String -> ValueType
getType key = Map.findWithDefault StringType key typeMap

mkConfig :: Maybe String      -- ^ Maybe a file extension to initialize defaults
         -> Maybe FilePath    -- ^ Maybe a path to a config (Desk) file
         -> [String]          -- ^ List of groups to include from the 'ConfigFile'
         -> Config            -- ^ 'Config' generated from command-line arguments
         -> IO Config
mkConfig mExt mDeskFile groups argsConf = do
    let defaultConf = [defaultConfig mExt]
    fgconfs <- case (mDeskFile, groups) of
        (Nothing, []) -> return []
        (Nothing, _) -> throwIO $ GroupsWithoutDesk groups
        (Just file, []) -> do
            (conf, _) <- parseConfigFile file
            return [conf]
        (Just file, _) -> do
            (conf, groupMap) <- parseConfigFile file
            gconfs <- forM groups $ \g -> do
                let mgconf = Map.lookup g groupMap
                maybe (throwIO $ GroupNotFound groupMap g) return mgconf
            return $ conf : gconfs
    let confs = defaultConf ++ fgconfs ++ [argsConf]
    return $ foldr (flip Map.union) Map.empty confs

{- Desk file handling -}

parseConfigFile :: FilePath -> IO (Config, Map String Config)
parseConfigFile file = do
    yaml <- join $ Y.decodeFile file
    ymap <- Y.fromMapping yaml
    conf <- getConfig ymap
    grps <- getGroups ymap
    return (conf, grps)

getConfig ymap = do
    conf <- sequence [tryReadValue k v | (k, Y.Scalar v) <- ymap]
    return (Map.fromList conf)

getGroups ymap = do
    case Y.lookupSequence "Groups" ymap of
        Nothing -> return Map.empty
        Just yseq -> Map.fromList <$> (forM yseq $ \omap -> do
            ymap <- Y.fromMapping omap
            name <- Y.lookupScalar "Name" ymap
            let ymap' = filter ((/= "Name") . fst) ymap
            conf <- getConfig ymap'
            return (name, conf))

{- Command-line option handling -}

options :: [OptDescr (String, Value)]
options = concatMap snd optionGroups

optionGroups :: [(String, [OptDescr (String, Value)])]
optionGroups = map (second (concatMap mkOptDescr))
    [ ("General options", generalSettings)
    , ("Common K options", commonKSettings)
    , ("Advanced K options", advancedKSettings)
    ]

mkOptDescr :: Setting -> [OptDescr (String, Value)]

mkOptDescr (Setting k@"print-help" _ desc) =
    [ Option ['h', '?'] ["help"] (NoArg (k, Bool True)) desc ]

mkOptDescr (Setting k@"print-version" _ desc) =
    [ Option ['v'] ["version"] (NoArg (k, Bool True)) desc ]

mkOptDescr (Setting k BoolType desc) =
    [ Option [] [k] (NoArg (k, Bool True)) desc
    , Option [] ["no-" ++ k] (NoArg (k, Bool False)) ""
    ]

mkOptDescr (Setting k StringType desc) =
    [ Option [] [k] (ReqArg (\s -> (k, String s)) "STRING") desc]

mkOptDescr (Setting k FileType desc) =
    [ Option [] [k] (ReqArg (\s -> (k, File s)) "FILE") desc]

parseOpts :: [String] -> IO (Config, [String])
parseOpts argv = case getOpt Permute options argv of
        (o, n, []) -> return (Map.fromList o, n)
        (_, _, errs) -> usageError errs 

usageError :: [String] -> IO a
usageError errs = do
    putStr $ concatMap ("krun: " ++) errs
    putStrLn "Type `krun --help' for more information."
    exitFailure

usage :: String
usage = "Usage: krun [groups] [options] <file>"

detailedHelp :: String
detailedHelp = usage
            ++ "\n\n"
            ++ concatMap groupHelp optionGroups
    where groupHelp (name, opts) = name ++ "\n" ++ usageInfo "" opts ++ "\n"

versionStr :: String
versionStr = "krun 0.3.0\nCopyright (C) 2011 David Lazar"
