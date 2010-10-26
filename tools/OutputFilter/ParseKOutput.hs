{- Module to parse the output from k
   Such output is constructed into named Cells and their contents, or Strings. See KOutput
   All formatting info (spaces, newlines, etc) with respect to the contents of cells is preserved,
   but the cells themselves do not preserve formatting. E.g.:
     <mycell> </mycell> === < mycell > </ mycell>

 -}

module ParseKOutput where
  import ByteStringUtils
  import Text.Parsec
  import Text.Parsec.ByteString
  import Control.Applicative ((<$>))
  import qualified Data.ByteString.Char8 as B

  type Name = ByteString
  type CellStack = [ByteString]

  data KOutput = Cell Name [KOutput] | String Name ByteString
    deriving (Show, Read, Eq)

  -- A string parser that has a stack of cell names for state (currenty unused), and outputs a KOutput
  type KOutputParser = Parsec ByteString CellStack KOutput

  -- Get rid of the maude header and stuff
  header :: Parsec ByteString CellStack ()
  header = manyTill anyChar (try (lookAhead beginCell)) >> return ()


  -- Open the file, and parse it. Return a list of parses (e.g. if there are multiple cells at the top level)
  parseKOutFile :: FilePath -> IO [KOutput]
  parseKOutFile fp = do input <- B.readFile fp
                        case runParser parseTop [] "" input of
                          Left err -> error $ show err
                          Right res -> return res

  parseTop :: Parsec ByteString CellStack [KOutput]
  parseTop = header >> many (try parseKOutput)

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
  parseString = peek >>= \name -> (String name . pack <$> many1 (noneOf "<"))
                              <|> (char '<' >> parseString >>= \k -> case k of String _ s -> return (String name (cons '<' s)))


  beginCell :: Parsec ByteString CellStack ByteString
  beginCell = do char '<' >> spaces
                 name <- pack <$> many1 alphaNum
                 push name
                 spaces >> char '>'
                 return name

  endCell :: Name -> Parsec ByteString CellStack ()
  endCell s = do spaces
                 char '<' >> spaces >> char '/' >> spaces
                 string (unpack s) >> spaces
                 char '>'
                 pop
                 return ()

  -- Combine strings when they were split due to a literal '<'
  -- When a '<' is parsed as part of the text (as opposed to a cell), everything before and everything after
  -- it will be in seperate Strings.
  combineStrings :: [KOutput] -> [KOutput]
  combineStrings (String n s1 : String _ s2 : ks) | B.head s2 == '<'
    = combineStrings (String n (s1 `append` s2) : ks)
  combineStrings (x:xs) = x : combineStrings xs
  combineStrings [] = []

  -- Stack-based operations on the state.
  push :: ByteString -> Parsec ByteString [ByteString] ()
  push s = modifyState (\l -> s : l)

  pop :: Parsec ByteString [ByteString] ()
  pop = modifyState $ \s -> (drop 1 s)

  peek :: Parsec ByteString [ByteString] ByteString
  peek = head <$> getState

  -- Test the parser
  testParser :: String -> IO ()
  testParser s = case runParser parseTop [] "" (pack s) of
                   Left err -> error $ show err
                   Right cs -> print cs


