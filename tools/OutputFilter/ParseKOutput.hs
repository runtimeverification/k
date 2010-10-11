{- Module to parse the output from k
   Such output is constructed into named Cells and their contents, or Strings. See KOutput
   All formatting info (spaces, newlines, etc) with respect to the contents of cells is preserved,
   but the cells themselves do not preserve formatting. E.g.:
     <mycell> </mycell> === < mycell > </ mycell>

 -}

module ParseKOutput where
  import Text.Parsec

  type Name = String
  type CellStack = [String]

  data KOutput = Cell Name [KOutput] | String String
    deriving (Show, Read, Eq)

  -- A string parser that has a stack of cell names for state (currenty unused), and outputs a KOutput
  type KOutputParser = Parsec String CellStack KOutput

  -- Open the file, and parse it. Return a list of parses (e.g. if there are multiple cells at the top level)
  parseKOutFile :: FilePath -> IO [KOutput]
  parseKOutFile fp = do input <- readFile fp
                        case runParser parseTop [] "" input of
                          Left err -> error $ show err
                          Right res -> return res

  parseTop :: Parsec String CellStack [KOutput]
  parseTop = many (try parseKOutput)

  -- Start parsing
  parseKOutput :: KOutputParser
  parseKOutput = spaces >> parseCell

  parseCell :: KOutputParser
  parseCell = do name <- beginCell
                 contents <- manyTill parseInternals (try (endCell name))
                 return $ Cell name (combineStrings contents)


  parseInternals :: KOutputParser
  parseInternals = try parseCell <|> parseString

  parseString :: KOutputParser
  parseString =  (many1 (noneOf "<") >>= return . String)
             <|> (char '<' >> parseString >>= \k -> case k of String s -> return (String ('<' : s)))


  beginCell :: Parsec String CellStack String
  beginCell = do char '<' >> spaces
                 name <- many1 alphaNum
                 -- push name
                 spaces >> char '>'
                 return name

  endCell :: Name -> Parsec String CellStack ()
  endCell s = do spaces
                 char '<' >> spaces >> char '/' >> spaces
                 string s >> spaces
                 char '>'
                 -- pop
                 return ()

  -- Combine strings when they were split due to a literal '<'
  -- When a '<' is parsed as part of the text (as opposed to a cell), everything before and everything after
  -- it will be in seperate Strings.
  combineStrings :: [KOutput] -> [KOutput]
  combineStrings (String s1 : String ('<':s2) : ks) = String (s1 ++ "<" ++ s2) : combineStrings ks
  combineStrings (x:xs) = x : combineStrings xs
  combineStrings [] = []

  -- Stack-based operations on the state.
  push :: String -> Parsec String [String] ()
  push s = modifyState (\l -> l ++ [s])

  pop :: Parsec String [String] ()
  pop = modifyState $ \s -> (dropLast s)

  peek :: Parsec String [String] String
  peek = getState >>= return . head

  dropLast = reverse . drop 1 . reverse


