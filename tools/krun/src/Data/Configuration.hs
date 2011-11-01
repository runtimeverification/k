{-# LANGUAGE DeriveDataTypeable #-}
module Data.Configuration where

import Control.Applicative ((<$>))
import Control.Arrow ((&&&), first, second)
import Control.Exception
import Control.Monad (forM, join)
import Data.Char (toLower, toUpper)
import Data.List (intercalate, partition, stripPrefix)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (catMaybes)
import qualified Data.Object as Y
import qualified Data.Object.Yaml as Y
import Data.Typeable
import Prelude hiding (catch)
import System.Console.GetOpt
import System.Environment
import System.Exit
import System.FilePath

import Distribution.Desk.Utils

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
    , Setting "io" BoolType "Use real IO when running the definition"
    , Setting "statistics" BoolType "Print Maude's rewrite statistics"
    ]

advancedKSettings :: [Setting]
advancedKSettings =
    [ Setting "compiled-def" FileType "Path to the compiled K definition"
    , Setting "do-search" BoolType "Search for all possible results"
    , Setting "maude-cmd" StringType "Maude command used to execute the definition (search, erewrite, search, ...)"
    , Setting "xsearch-pattern" StringType "Search pattern"
    , Setting "output-mode" StringType "How to display Maude results (options are none, raw, and pretty)"
    ]

-- | Configuration settings that can be initialized using 
-- the input program's extension.
mkExtConfig :: Maybe String -> Config
mkExtConfig Nothing = Map.empty
mkExtConfig (Just ext') = let ext = map toUpper . dropWhile (== '.') $ ext' in 
    Map.fromList $
    [ ("main-module", String ext)
    , ("syntax-module", String $ ext ++ "-SYNTAX")
    ]

mkInitConfig :: FilePath -> IO Config
mkInitConfig dir = do
    maudeFiles <- getFilesWithExt ".maude" dir
    let compiledFiles = catMaybes . map splitDef $ maudeFiles
    case compiledFiles of
        [] -> return Map.empty
        [(lang, def)] -> return $ Map.fromList
            [ ("main-module", String $ map toUpper lang)
            , ("syntax-module", String $ map toUpper lang ++ "-SYNTAX")
            , ("compiled-def", File def)
            ]
        multiple -> multiDef multiple
            
    where splitDef f
            = let f' = takeFileName f in
              case stripPrefix (reverse "-compiled.maude") (reverse f') of
                Nothing -> Nothing
                Just x -> Just $ (reverse x, f)

          multiDef l = die $ "Multiple compiled definitions found.\n"
                           ++ "Please use only one of: "
                           ++ intercalate " " (map show l)


resolveCompiledDef :: Config -> IO Config
resolveCompiledDef config = do
    if Map.member "compiled-def" config
        then return config
        else do
            case Map.lookup "main-module" config of
                Just (String mainMod) -> return $ Map.insert "compiled-def"
                  (File $ map toLower mainMod ++ "-compiled.maude") config
                _ -> return config

allSettings :: [Setting]
allSettings = metadataSettings ++ generalSettings ++ commonKSettings ++ advancedKSettings

typeMap :: Map String ValueType
typeMap = Map.fromList $ map (\s -> (settingName s,  settingType s)) allSettings

getType :: String -> ValueType
getType key = Map.findWithDefault StringType key typeMap

mkConfig :: Maybe FilePath    -- ^ Maybe a path to a config (Desk) file
         -> [String]          -- ^ List of groups to include from the 'ConfigFile'
         -> Config            -- ^ 'Config' generated from command-line arguments
         -> IO Config
mkConfig mDeskFile groups argsConfig = do
--    let extConfig = mkExtConfig mExt
    initConfig <- mkInitConfig "."
    kbase <- getEnv "K_BASE"
    (defaultConfig, defaultGroups) <- parseConfigFile $ kbase </> "tools" </> "global-defaults.desk"
    (deskConfig, deskGroups) <- maybe (return (Map.empty, Map.empty)) parseConfigFile mDeskFile
    let groupMap = deskGroups `Map.union` defaultGroups
    groupConfigs <- forM groups $ \g -> do
        let mgconf = Map.lookup g groupMap
        maybe (throwIO $ GroupNotFound groupMap g) return mgconf
    let configs = initConfig : defaultConfig : deskConfig : groupConfigs ++ [argsConfig]
    let config = foldr (flip Map.union) Map.empty configs
    config' <- resolveCompiledDef config
    return config'

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
    case Y.lookupSequence "groups" ymap of
        Nothing -> return Map.empty
        Just yseq -> Map.fromList <$> (forM yseq $ \omap -> do
            ymap <- Y.fromMapping omap
            name <- Y.lookupScalar "name" ymap
            let ymap' = filter ((/= "name") . fst) ymap
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

parseOpts :: [String] -> IO (Config, [String], [String])
parseOpts argv = case getOpt' Permute options argv of
        (o, n, u, []) -> return (Map.fromList o, n, u)
        (_, _, _, errs) -> usageError errs 

usageError :: [String] -> IO a
usageError errs = do
    putStr $ concatMap ("krun: " ++) errs
    putStrLn "Type `krun --help' for more information."
    exitFailure

usage :: String
usage = "Usage: krun [options] <file>"

detailedHelp :: String
detailedHelp = usage
            ++ "\n\n"
            ++ concatMap groupHelp optionGroups
            ++ additionalHelp
    where groupHelp (name, opts) = name ++ "\n" ++ usageInfo "" opts ++ "\n"

additionalHelp :: String
additionalHelp = intercalate "\n"
    [ "krun also has several predefined option groups such as --search,"
    , "--config, and --no-config. These predefined groups can be found in"
    , "$K_BASE/tools/global-defaults.desk"
    , ""
    , "Currently, krun attempts to infer the main-module and syntax-module"
    , "settings using the input program's file extension. For example, if"
    , "krun is called on program foo.bar and if these settings are not"
    , "overridden elsewhere (via the command-line or a .desk file), then"
    , "krun assumes:"
    , ""
    , "main-module: BAR"
    , "syntax-module: BAR-SYNTAX"
    , ""
    , "If the input program lacks a file extension, or if the defaults"
    , "inferred from the program's file extension are not good enough,"
    , "main-module and syntax-module MUST be set explicitly."
    , ""
    , "Finally, for the time being, krun must be run from the directory that"
    , "contains the definition's .k directory, which contains essential"
    , "information on how to parse the input programs. The compiled"
    , "definition, ${main-module}-compiled.maude by default, is also assumed"
    , "to be in the current working directory. Future versions of the tool"
    , "will not have this limitation."
    ]

versionStr :: String
versionStr = "krun 0.3.0\nCopyright (C) 2011 David Lazar"
