{- Module that parses the cell-content strings and infixifies the operators -}

module InfixOperators where
  import Text.Parsec
  import ParseKOutput
  import Control.Applicative ((<$>))
  import Data.List.Utils

  data Content = Operator Name [Content] | StringContent String | ParenedContent [Content]
    deriving (Show)

  type ContentState = Int

  type ContentParser = Parsec String ContentState

  parseContentsTop :: ContentParser [Content]
  parseContentsTop = many1 parseContents

  parseOperator :: ContentParser Content
  parseOperator = do name     <- beginOperator
                     contents <- manyTill parseContents (try endOperator)
                     return $ Operator name contents
              <?> "an operator"

  parseContents :: ContentParser Content
  parseContents = (try parseOperator) <|> try parseStringContent <|> try acceptRest

  parseStringContent = StringContent <$> many1 (noneOf "()")
                   <|> parseNonOpParens
                   <?> "string content"

  parseNonOpParens :: ContentParser Content
  parseNonOpParens = do openParen
                        innards <- parseContentsTop
                        endParen
                        return . ParenedContent $ innards


  beginOperator :: ContentParser Name
  beginOperator = do string "('"
                     name <- many1 $ noneOf ")"
                     string ")."
                     parseLabel
                     openParen
                     return name
               <?> "beginning of operator"

  endOperator :: ContentParser ()
  endOperator = endParen <?> "end of operator"

  -- Just accept the rest of the input as a StringContent
  -- This is because text and cells may be intermixed, e.g. "List ( <cell> <cell> )" would be split into two seperate
  -- strings with the cells in them, e.g. ["List ( ", Cell, Cell, " ) "]
  acceptRest = StringContent <$> many1 anyChar


  parseLabel :: ContentParser Name
  parseLabel = anyChar `manyTill` string "Label"

  commaCommaSep p = p `sepBy` string ",,"

  openParen = do char '('
                 incr

  endParen = do char ')'
                decr

  incr = modifyState $ \i -> i + 1
  decr = modifyState $ \i -> i - 1

  test :: String -> IO ()
  test s = case runParser parseContentsTop 0 "" s of
             Left err -> print err
             Right cs  -> print $ postProcess cs

  wrap :: Char -> String -> Char -> String
  wrap l s r = l : (s ++ [r])


  -- todo: do the below with generics

  postProcess :: [Content] -> [Content]
  postProcess = eliminateEmptySCs . seperateSCs . globSCs . flattenParenContent

  -- Concat paren content down
  flattenParenContent :: [Content] -> [Content]
  flattenParenContent (ParenedContent pcs : cs) = [StringContent "("] ++ flattenParenContent pcs ++ [StringContent ")"] ++ flattenParenContent cs
  flattenParenContent (Operator n ocs : cs)     = Operator n (flattenParenContent ocs) : flattenParenContent cs
  flattenParenContent (c : cs)                  = c : flattenParenContent cs
  flattenParenContent []                        = []

  -- Condense adjacent StringContents together.
  -- Use this before seperating on ,, and not after
  globSCs :: [Content] -> [Content]
  globSCs (StringContent s : StringContent s2 : xs) = globSCs (StringContent (s ++ s2) : xs)
  globSCs (StringContent s : xs)                    = StringContent s : globSCs xs
  globSCs (Operator n cs : xs)                      = Operator n (globSCs cs) : globSCs xs
  globSCs []                                        = []

  -- Seperate on the ,,
  seperateSCs :: [Content] -> [Content]
  seperateSCs (StringContent s : cs) = (map StringContent $ split ",," s) ++ seperateSCs cs
  seperateSCs (Operator n cs : rest) = Operator n (seperateSCs cs) : seperateSCs rest
  seperateSCs []                     = []

  -- the name says it all
  eliminateEmptySCs :: [Content] -> [Content]
  eliminateEmptySCs (StringContent "" : cs) = eliminateEmptySCs cs
  eliminateEmptySCs (Operator n cs : rest)  = Operator n (eliminateEmptySCs cs) : eliminateEmptySCs rest
  eliminateEmptySCs (c : cs)                = c : eliminateEmptySCs cs
  eliminateEmptySCs []                      = []

  -- Convert back into a string
  contentToString :: Content -> String
  contentToString (StringContent s) = s
  contentToString (Operator name cs) | shouldInfix name  = join (" " ++ init (tail name) ++ " ")  innards
                                     | shouldMixfix name = join " " $ intermix (seperateMixfix name) innards
                                     | otherwise         = name ++ "(" ++ join ",," innards ++ ")"
    where innards = map contentToString cs

  shouldInfix ('_':cs) = last cs == '_' && '_' `notIn` init cs
    where x `notIn` xs = not $ x `elem` xs
  shouldInfix _ = False

  shouldMixfix s = '_' `elem` s

  seperateMixfix :: String -> [String]
  seperateMixfix s = "_" `split` (deleteAll '`' s)



  -- Intermix two string lists. The first argument should be of size one greater than the second
  intermix :: [a] -> [a] -> [a]
  intermix (l:ls) (r:rs) = l : r : intermix ls rs
  intermix [left] [] = [left]
  intermix _ _ =  error "Output contains the wrong number of arguments for a mixfix operator"

  -- Do the whole shebang
  makeInfix :: String -> String
  makeInfix s = case runParser parseContentsTop 0 "" s of
                  Left err -> error $ show err
                  Right cs -> join " " . map contentToString $ postProcess cs


  -- Delete all occurrences
  deleteAll :: Eq a => a -> [a] -> [a]
  deleteAll x = filter ((/=) x)
