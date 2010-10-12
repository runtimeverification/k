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

module ParseConfig where
  import Data.Yaml.Syck
  import Control.Applicative
  import Data.Char
  import Control.Arrow

  type CellName = String
  type Configuration = [CellConfig]

  type CellConfig = (String, CellConfigRhs)

  -- add more to this to support more customizations
  data CellConfigRhs = Show
                     | Hide
                     | Lines Int
                     | RecursiveShow
                     | RecursiveHide
    deriving (Show)

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
  extractConfiguration = (map extractCellConfig . unMap)

  -- I use arrows because I'm awesome. See the commented out version for the more clear version
  extractCellConfig :: (YamlLite, YamlLite) -> CellConfig
  extractCellConfig = arr unStr *** arr readConfig
  -- extractCellConfig (l,r) = (unStr l, readConfig r)


  -- Extend the below function to add more functionality
  readConfig :: YamlLite -> CellConfigRhs
  readConfig (Str s) | compareStr s doShow    = Show
                     | compareStr s doHide    = Hide
                     | compareStr s doHideRec = RecursiveHide
                     | compareStr s doShowRec = RecursiveShow
                     | otherwise              = error $ "Unknown value: " ++ s
    where doShow    = ["yes", "y", "show", "true", "t"]
          doHide    = ["no", "n", "hide", "false", "f"]
          doHideRec = ["hide-recursive", "recursive-hide", "recursively-hide", "hide-recursively"]
          doShowRec = ["show-recursive", "recursive-show", "recursively-show", "show-recursively"]

  readConfig (Map [(Str key, Str val)]) | compareStr key ["lines", "keep"] && areNumbers val = Lines (read val)
  readConfig (Map _) = Show

  -- Compare the contents of the config item to see if it occurs in passed strings.
  compareStr :: String -> [String] -> Bool
  compareStr s ss = canonicalize s `elem` map canonicalize ss
    where canonicalize = map toLower

  areNumbers :: String -> Bool
  areNumbers = and . map isDigit

  getConfig :: FilePath -> IO Configuration
  getConfig fp = extractConfiguration <$> parseYamlFileLite fp

  -- Data "destructors", not so safe and meant to be expanded with ones raising more useful errors
  -- Todo: implement a more robust solution using generics
  unSeq :: YamlLite -> [YamlLite]
  unSeq (Seq s) = s

  unMap :: YamlLite -> [(YamlLite,YamlLite)]
  unMap (Map m) = m

  unStr :: YamlLite -> String
  unStr (Str s) = s