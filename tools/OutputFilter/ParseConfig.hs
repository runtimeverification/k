{-
  Parse the config file given, building up the desired Configuration
  Config files are yaml documents of the form:
    <cellname>: [y(es)|n(o)]
    ...
  to configure whether to display that cell.
  See examples/example.yml
  If a cell is flagged as "yes", then it will be shown (this has no effect on its children)
  Current default behavior is to not show anything not explicitly told to be shown
-}

{-# LANGUAGE OverloadedStrings #-}

module ParseConfig
  ( getConfig
  , Configuration, CellName, CellConfigRhs(..), Style(..), Color(..), Substitution(..), ColorPlace(..)
  , Underline(..), Bold(..)
  )where
  import Data.Yaml.YamlLight
  import Control.Applicative
  import Control.Monad
  import Data.Char
  import qualified Data.ByteString.Char8 as B
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons)
  import Control.Arrow
  import Data.List
  import qualified Data.Map as Map
  import Text.Regex.Less
--  import Text.Regex.PCRE.Light.Char8

  type CellName = ByteString
  type Configuration = Map CellName CellConfigRhs
  type Map = Map.Map

  -- Add more to this to support more customizations
  data CellConfigRhs = Show
                     | Hide
                     | RecursiveHide
                     | Configs { keepLines     :: Maybe Int
                               , keepChars     :: Maybe Int
                               , cellStyle     :: Maybe Style
                               , textStyle     :: Maybe Style
                               , substitutions :: Maybe [Substitution]
                               }
                     | Options { globalSubstitutions :: Maybe [Substitution]
                               , spacelessCells      :: Maybe Bool
                               , infixify            :: Maybe Bool
                               , lineEnd             :: Maybe ByteString
                               }
    deriving (Show)

  data Style = Style { foreground :: Maybe Color
                     , background :: Maybe Color
                     , underlined :: Maybe Underline
                     , bolded     :: Maybe Bold
                     }
    deriving Show

  data Underline = Underline | DeUnderline
    deriving Show

  data Bold = Bold | DeBold
    deriving Show

  data Color = Black | Red | Green | Yellow | Blue | Magenta | Cyan | White
             | Dullblack | Dullred | Dullgreen | Dullyellow | Dullblue | Dullmagenta
             | Dullcyan | Dullwhite
    deriving (Show, Read)

  data ColorPlace = Background | Foreground

  data Substitution = Substitution ByteString ByteString
    deriving (Show, Eq)

  -- A Yaml tree without superfluous info and types

  -- | Given a filename, will read that file, parse it as yaml, and extract a configuration from it.
  getConfig :: FilePath -> IO Configuration
  getConfig fp = do conf <- extractConfiguration <$> parseYamlFile fp
                    case conf of
                      Just c  -> return c
                      Nothing -> error $ "Unable to extract a configuration from " ++ fp


  -- Get the configuration
  extractConfiguration :: YamlLight -> Maybe Configuration
  extractConfiguration yl = Map.mapKeys unsafeUnStr <$> Map.mapWithKey convertToCellRhs <$> unMap yl


  -- Convert the second argument from a YamlLight to a CellConfigRhs. There is a special-case cell
  -- called "options" for its namesake, hence the key being passed in as well
  convertToCellRhs :: YamlLight -> YamlLight -> CellConfigRhs
  convertToCellRhs key val | unsafeUnStr key == "options" = readOptions val
                           | otherwise                    = readConfig val

  readOptions m = Options (getGlobalSubs <$> lookupConf doGlobalSubs m)
                          (getBool       <$> lookupConf doSpacelessCells m)
                          (getBool       <$> lookupConf doInfixity m)
                          (getString     <$> lookupConf doLineEnd m)

  readConfig :: YamlLight -> CellConfigRhs
  readConfig (YStr s)   = readSingleEntry s
  readConfig m@(YMap _) = readMap m

  readMap :: YamlLight -> CellConfigRhs
  readMap m = Configs (getNum   <$> lookupConf doKeep m)
                      (getNum   <$> lookupConf doKeepChars m)
                      (getStyle <$> lookupConf doCellStyle m)
                      (getStyle <$> lookupConf doTextStyle m)
                      Nothing -- extend me to do local substitutions

  lookupConf :: [ByteString] -> YamlLight -> Maybe YamlLight
  lookupConf ss = lookupYLWith ((flip compareStr) ss . unsafeUnStr)


  {- Functions to read the value and construct the desired part of the end configuration -}

  getGlobalSubs ys = case combineSequencedMaps ys of
                       Just subs -> map mkSubstitution subs
                       Nothing   -> error "User error: please specify substitutions as a (yaml) sequnce of key:value pairs"

  mkSubstitution (key,val) = Substitution (getString key) (getString val)


  getBool :: YamlLight -> Bool
  getBool = tryTerminalApply readBool "Internal error: getBool called on non-terminal value"

  getNum :: YamlLight -> Int
  getNum = tryTerminalApply readNumber "Internal error: getNum called on non-terminal value"

  getColor :: YamlLight -> Color
  getColor = tryTerminalApply readColor "Internal error: getColor called on non-terminal value"

  getString :: YamlLight -> ByteString
  getString = tryTerminalApply id "Internal error: getString called on non-terminal value"

  getStyle :: YamlLight -> Style
  getStyle m = Style (getColor     <$> lookupConf doForeground m)
                     (getColor     <$> lookupConf doBackground m)
                     (getUnderline <$> lookupConf doUnderline m)
                     (getBold      <$> lookupConf doBold m)

  getUnderline :: YamlLight -> Underline
  getUnderline (YStr s) | s `compareStr` doUnderline   = Underline
                        | s `compareStr` doDeUnderline = DeUnderline
                        | otherwise                    = error $ "Unable to parse: " ++ unpack s ++ " as an underline style"

  getBold :: YamlLight -> Bold
  getBold (YStr s) | s `compareStr` doBold   = Bold
                   | s `compareStr` doDeBold = DeBold
                   | otherwise               = error $ "Unable to parse: " ++ unpack s ++ " as an bold style"

  isColor :: ByteString -> Bool
  isColor = flip compareStr $ [ "Black", "Red", "Green", "Yellow", "Blue", "Magenta", "Cyan"
                              , "White", "Dullblack", "Dullred", "Dullgreen", "Dullyellow"
                              , "Dullblue", "Dullmagenta", "Dullcyan", "Dullwhite"
                              ]

  readSingleEntry :: ByteString -> CellConfigRhs
  readSingleEntry s | compareStr s doShow    = Show
                    | compareStr s doHide    = Hide
                    | compareStr s doHideRec = RecursiveHide
--                    | compareStr s doShowRec = RecursiveShow
                    | otherwise              = error $ "Unknown value: " ++ unpack s

  -- In the yaml file, there are many acceptable ways to say something, the following are for expressing those
  -- ways
  doGlobalSubs     = ["global-substitutions", "global-subs"] ++ doSubstitutions
  doSpacelessCells = ["spaceless-cells", "spaceless", "spacelessCells"]
  doInfixity       = ["infixity", "infixify", "infix"]
  doKeep           = ["lines", "keep", "keep-lines", "keepLines"]
  doKeepChars      = ["characters", "chars", "keepChars", "keep-chars", "keep-characters"]
  doCellStyle      = ["cell-color", "cell-style"]
  doTextStyle      = ["text-color", "text-style"]
  doUnderline      = ["underline", "under-line", "underlined"] ++ doTrue
  doDeUnderline    = ["deunderline", "de-underline", "de-under-line"] ++ doFalse
  doForeground     = ["foreground"]
  doBackground     = ["background"]
  doBold           = ["bold", "embolden", "bolded"] ++ doTrue
  doDeBold         = ["debold", "de-bold", "un-bold", "unbold"] ++ doFalse
  doShow           = doTrue ++ ["show"]
  doHide           = doFalse ++ ["hide"]
  doHideRec        = ["hide-recursive", "recursive-hide", "recursively-hide", "hide-recursively"]
  doTrue           = ["yes", "y", "t", "true"]
  doFalse          = ["no", "n", "f", "false"]
  doShowRec        = ["show-recursive", "recursive-show", "recursively-show", "show-recursively"]
  doSubstitutions  = ["subs", "subst", "substitutions", "sub"]
  doLineEnd        = ["lineend", "line-end", "line-end-str", "line-end-string", "lineendstr", "lineendstring"
                     ,"endline", "end-line"]

  -- Compare the contents of the config item to see if it occurs in passed strings.
  compareStr :: ByteString -> [ByteString] -> Bool
  compareStr s ss = canonicalize s `elem` map canonicalize ss

  -- Canonical form, also is in a form ready to be read in
  canonicalize :: ByteString -> ByteString
  canonicalize s = case uncons s of Just (c, cs) -> toUpper c `cons` B.map toLower cs
                                    Nothing      -> B.empty

  areNumbers :: ByteString -> Bool
  areNumbers = B.all isDigit


  readBool :: ByteString -> Bool
  readBool s | compareStr s doTrue  = True
             | compareStr s doFalse = False
             | otherwise            = error $ "Unable to read " ++ unpack s ++ " as a truth value"

  readNumber s = tryRead areNumbers s $ "Unable to parse: " ++ unpack s ++ " as a number"

  readColor s = tryRead isColor s $ "Unable to parse: " ++ unpack s ++ " as a color"

  -- Read utilities
  tryRead :: Read a => (ByteString -> Bool) -> ByteString -> String -> a
  tryRead p s err = if p s then read (unpack (canonicalize s)) else error err

  tryReadInt :: ByteString -> String -> Int
  tryReadInt = tryRead areNumbers

  -- Try to run f on a YamlLight's String (if it is a terminal), else error out with errStr
  tryTerminalApply :: (ByteString -> a) -> String -> YamlLight -> a
  tryTerminalApply f errStr (YStr s) = f s
  tryTerminalApply _ errStr _        = error errStr

  tryMapApply :: ((Map.Map YamlLight YamlLight) -> a) -> String -> YamlLight -> a
  tryMapApply f _ (YMap m) = f m
  tryMapApply _ errStr _  = error errStr

  unsafeUnStr (YStr s) = s
  unsafeUnStr _        = error "Expecting a terminal"