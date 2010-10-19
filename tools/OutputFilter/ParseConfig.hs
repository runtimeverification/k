{-
  Parse the config file given, building up the desired Configuration
  Config files are yaml documents of the form:
    <cellname>: [y(es)|n(o)]
    ...
  to configure whether to display that cell.
  See examples/example.yml
  If a cell is flagged as "yes", then it will be shown (this has no effect on its children)
g  Current default behavior is to not show anything not explicitly told to be shown
-}

{-# LANGUAGE OverloadedStrings #-}

module ParseConfig where
  import Data.Yaml.Syck
  import Control.Applicative
  import Control.Monad
  import Data.Char
  import Control.Arrow
  import Data.List
  import qualified Data.Map as Map
--  import Text.Regex.PCRE.Light.Char8

  type CellName = String
  type Configuration = Map CellName CellConfigRhs
  type Map = Map.Map

  type CellConfig = (CellName, CellConfigRhs)

  -- add more to this to support more customizations
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

  -- data Substitution = Substitution Regex String
  --   deriving (Show, Eq)

  data Substitution = Substitution String String
    deriving (Show, Eq)

  -- A Yaml tree without superfluous info and types
  data YamlLite = Map [(YamlLite, YamlLite)]
                | Seq [YamlLite]
                | Str String
                | Nil
    deriving (Show)


  -- Convert to the lighter representation
  yamlNodeToLite :: YamlNode -> YamlLite
  yamlNodeToLite = yamlElemToLite . n_elem

  yamlElemToLite :: YamlElem -> YamlLite
  yamlElemToLite (EMap ms)  = Map $ map (\(a,b) -> (yamlNodeToLite a, yamlNodeToLite b)) ms
  yamlElemToLite (ESeq s)   = Seq $ map yamlNodeToLite s
  yamlElemToLite (EStr buf) = Str $ unpackBuf buf
  yamlElemToLite (ENil)     = Nil

  parseYamlFileLite fp = yamlNodeToLite <$> parseYamlFile fp


  -- Get the configuration
  extractConfiguration :: YamlLite -> Configuration
  extractConfiguration = Map.fromList . map extractCellConfig . unMap

  -- I use arrows because I'm awesome. See the commented out version for the more clear version
  -- There is a special-case cell called "global-substitutions" for its namesake
  extractCellConfig :: (YamlLite, YamlLite) -> CellConfig
  extractCellConfig pair | isOptionsCell pair = (arr unStr *** arr readOptions) pair
                         | otherwise          = (arr unStr *** arr readConfig) pair
  -- extractCellConfig (l,r) = (unStr l, readConfig r)

  mkSubstitution :: (YamlLite, YamlLite) -> Substitution
  mkSubstitution (key,val) = Substitution (unStr key) (unStr val)

  readOptions (Map xs) = Options (getGlobalSubs     =<< (lookupConf doGlobalSubs xs))
                                 (getBool           <$> (lookupConf doSpacelessCells xs))
                                 (getBool           <$> (lookupConf doInfixity xs))
    where doGlobalSubs     = ["global-substitutions", "global-subs"] ++ doSubstitutions
          doSpacelessCells = ["spaceless-cells", "spaceless", "spacelessCells"]
          doInfixity       = ["infixity", "infixify", "infix"]

  doSubstitutions = ["subs", "subst", "substitutions", "sub"]

  getGlobalSubs (Map xs) = Just $ map mkSubstitution xs
  getGlobalSubs _        = Nothing

  getBool (Str s) = readBool s


  isOptionsCell (key, _) = unStr key == "options"

  --isGlobalSub (key, val) = unStr key == "global-substitutions"

  -- Extend the below function to add more functionality
  readConfig :: YamlLite -> CellConfigRhs
  readConfig (Str s) = readSingleEntry s
  readConfig (Map map) = readMap map

  readMap :: [(YamlLite,YamlLite)] -> CellConfigRhs
  readMap xs = Configs (getLines <$> (lookupConf doKeep xs))
                       (getChars <$> (lookupConf doKeepChars xs))
                       (getStyle <$> (lookupConf doCellStyle xs))
                       (getStyle <$> (lookupConf doTextStyle xs))
                       Nothing -- extend me to do local substitutions
    where doKeep          = ["lines", "keep", "keep-lines", "keepLines"]
          doKeepChars     = ["characters", "chars", "keepChars", "keep-chars", "keep-characters"]
          doCellStyle     = ["cell-color", "cell-style"]
          doTextStyle     = ["text-color", "text-style"]
          doSubstitutions = ["local-substitutions", "substitutions"]

  lookupConf ss map = snd <$> (find ((flip compareStr) ss . unStr . fst) $ map)

  getLines :: YamlLite -> Int
  getLines (Str s) = tryRead areNumbers s $ "Unable to parse: " ++ s ++ " as a number"
  getLines _ = error $ "Internal error: getLines called on non-terminal value"

  getChars :: YamlLite -> Int
  getChars (Str s) = tryRead areNumbers s $ "Unable to parse: " ++ s ++ " as a number"
  getChars _ = error $ "Internal error: getChars called on non-terminal value"

  getStyle :: YamlLite -> Style
  getStyle (Map xs) = Style (getColor      <$> (lookupConf doForeground xs))
                             (getColor     <$> (lookupConf doBackground xs))
                             (getUnderline <$> (lookupConf doUnderline xs))
                             (getBold      <$> (lookupConf doBold xs))
    where doForeground = ["foreground"]
          doBackground = ["background"]
          doUnderline  = ["underline", "underlined"]
          doBold       = ["bold"]

  getColor :: YamlLite -> Color
  getColor (Str s) = tryRead isColor s $ "Unable to parse: " ++ s ++ " as a color"
  getColor _ = error $ "Internal error: getColor called on non-terminal value"

  getUnderline :: YamlLite -> Underline
  getUnderline (Str s) | s `compareStr` doUnderline   = Underline
                       | s `compareStr` doDeUnderline = DeUnderline
                       | otherwise                    = error $ "Unable to parse: " ++ s ++ " as an underline style"
    where doUnderline   = ["underline", "under-line", "underlined"] ++ doTrue
          doDeUnderline = ["deunderline", "de-underline", "de-under-line"]

  getBold :: YamlLite -> Bold
  getBold (Str s) | s `compareStr` doBold   = Bold
                  | s `compareStr` doDeBold = DeBold
                  | otherwise               = error $ "Unable to parse: " ++ s ++ " as an bold style"
    where doBold   = ["bold", "embolden", "bolded"] ++ doTrue
          doDeBold = ["debold", "de-bold", "un-bold", "unbold"]


  isColor :: String -> Bool
  isColor = flip compareStr $ [ "Black", "Red", "Green", "Yellow", "Blue", "Magenta", "Cyan"
                              , "White", "Dullblack", "Dullred", "Dullgreen", "Dullyellow"
                              , "Dullblue", "Dullmagenta", "Dullcyan", "Dullwhite"
                              ]

  readSingleEntry :: String -> CellConfigRhs
  readSingleEntry s | compareStr s doShow    = Show
                    | compareStr s doHide    = Hide
                    | compareStr s doHideRec = RecursiveHide
--                    | compareStr s doShowRec = RecursiveShow
                    | otherwise              = error $ "Unknown value: " ++ s
    where doShow    = doTrue ++ ["show"]
          doHide    = doFalse ++ ["hide"]
          doHideRec = ["hide-recursive", "recursive-hide", "recursively-hide", "hide-recursively"]
          doShowRec = ["show-recursive", "recursive-show", "recursively-show", "show-recursively"]

  doTrue  = ["yes", "y", "t", "true"]
  doFalse = ["no", "n", "f", "false"]


  -- Compare the contents of the config item to see if it occurs in passed strings.
  compareStr :: String -> [String] -> Bool
  compareStr s ss = canonicalize s `elem` map canonicalize ss

  -- Canonical form, also is in a form ready to be read in
  canonicalize (c:cs) = toUpper c : map toLower cs
  canonicalize []     = []

  areNumbers :: String -> Bool
  areNumbers = and . map isDigit

  getConfig :: FilePath -> IO Configuration
  getConfig fp = extractConfiguration <$> parseYamlFileLite fp

  readBool :: String -> Bool
  readBool s | compareStr s doTrue  = True
             | compareStr s doFalse = False
             | otherwise            = error $ "Unable to read " ++ s ++ " as a truth value"

  -- Data "destructors", not so safe and meant to be expanded with ones raising more useful errors
  -- Todo: implement a more robust solution using generics
  unSeq :: YamlLite -> [YamlLite]
  unSeq (Seq s) = s

  unMap :: YamlLite -> [(YamlLite,YamlLite)]
  unMap (Map m) = m

  unStr :: YamlLite -> String
  unStr (Str s) = s

  -- Read utilities
  tryRead :: Read a => (String -> Bool) -> String -> String -> a
  tryRead p s err = if p s then read (canonicalize s) else error err

  -- tryReadBool :: String -> String -> Bool
  -- tryReadBool = tryRead isBool

  tryReadInt :: String -> String -> Int
  tryReadInt = tryRead areNumbers