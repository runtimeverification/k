{-
  Parse the config file given, building up the desired Configuration
  Config files are yaml documents of the form:
    <cellname>: [y(es)|n(o)]
    ...
  to configure whether to display that cell.
  See examples/example.yml
  If a cell is flagged as "no", then it will not be shown (neither will its children)
  Current default behavior is to show anything not explicitly told to be hidden
-}

module ParseConfig where
  import Data.Yaml.Syck
  import Control.Applicative
  import Data.Char

  type CellName = String
  type Configuration = [CellConfig]

  type CellConfig = (String, CellConfigRhs)

   -- add more to this to support more customizations
  data CellConfigRhs = Yes
                     | No
    deriving (Show)

  -- A Yaml tree without superfluous info and types
  data YamlLite = Map [(YamlLite, YamlLite)]
                | Seq [YamlLite]
                | Str String
                | Nil
    deriving (Show)

  yamlNodeToLite :: YamlNode -> YamlLite
  yamlNodeToLite = yamlElemToLite . n_elem

  yamlElemToLite :: YamlElem -> YamlLite
  yamlElemToLite (EMap ms)  = Map $ map (\(a,b) -> (yamlNodeToLite a, yamlNodeToLite b)) ms
  yamlElemToLite (ESeq s)   = Seq $ map yamlNodeToLite s
  yamlElemToLite (EStr buf) = Str $ unpackBuf buf
  yamlElemToLite (ENil)     = Nil

  parseYamlFileLite fp = yamlNodeToLite <$> parseYamlFile fp

  extractConfiguration :: YamlLite -> Configuration
  extractConfiguration = (map extractCellConfig . unSeq)

  extractCellConfig :: YamlLite -> CellConfig
  extractCellConfig yl = ((unStr . fst . head . unMap) yl, (readConfig . unStr . snd . head . unMap) yl)

  readConfig :: String -> CellConfigRhs
  readConfig s | canonicalize s `elem` ["yes", "y"] = Yes
               | canonicalize s `elem` ["no", "n"]  = No
               | otherwise                          = error $ "Unknown value: " ++ s
    where canonicalize = map toLower

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