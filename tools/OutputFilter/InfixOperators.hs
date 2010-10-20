{- Module that parses the cell-content strings and infixifies the operators -}

module InfixOperators where
  import ParseKOutput
  import ByteStringUtils
  import Text.Parsec
  import Text.Parsec.ByteString
  import Control.Applicative ((<$>))
  import qualified Data.List.Utils as MH
  import Control.Monad.Identity (Identity)
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons, append, singleton)
  import qualified Data.ByteString.Char8 as B

  data Content = Operator Name [Content] | StringContent ByteString | ParenedContent [Content]
    deriving (Show)

  type ContentState = Int

  type ContentParser = Parsec ByteString ContentState

  parseContentsTop :: ContentParser [Content]
  parseContentsTop = many1 parseContentsNotAll

  parseOperator :: ContentParser Content
  parseOperator = do name     <- beginOperator
                     contents <- manyTill parseContents (try endOperator)
                     return $ Operator name contents
              <?> "an operator"

  parseContents :: ContentParser Content
  parseContents = (try parseOperator) <|> try parseStringContent  <|> try acceptRest

  parseContentsNotAll :: ContentParser Content
  parseContentsNotAll = (try parseOperator) <|> try parseStringContent

  parseStringContent :: ContentParser Content
  parseStringContent = StringContent . pack <$> many1 (noneOf "()")
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
                     return $ pack name
               <?> "beginning of operator"

  endOperator :: ContentParser ()
  endOperator = endParen <?> "end of operator"

  -- Just accept the rest of the input as a StringContent
  -- This is because text and cells may be intermixed, e.g. "List ( <cell> <cell> )" would be split into two
  -- seperate strings with the cells in them, e.g. ["List ( ", Cell, Cell, " ) "]
  acceptRest :: ContentParser Content
  acceptRest = StringContent . pack <$> many1 anyChar


  parseLabel :: ContentParser Name
  parseLabel = pack <$> anyChar `manyTill` string "Label"

  commaCommaSep p = p `sepBy` string ",,"

  openParen = do char '('
                 incr

  endParen = do char ')'
                decr

  incr = modifyState $ \i -> i + 1
  decr = modifyState $ \i -> i - 1

  test :: String -> IO ()
  test s = case runParser parseContentsTop 0 "" (pack s) of
             Left err -> print err
             Right cs  -> print $ postProcess cs

  wrap :: Char -> ByteString -> Char -> ByteString
  wrap l s r = cons l $ s `append` singleton r


  -- todo: do the below with generics

  postProcess :: [Content] -> [Content]
  postProcess = eliminateEmptySCs . seperateSCs . globSCs . flattenParenContent

  -- Concat paren content down
  flattenParenContent :: [Content] -> [Content]
  flattenParenContent (ParenedContent pcs : cs) = [StringContent (pack "(")] ++ flattenParenContent pcs ++ [StringContent (pack ")")] ++ flattenParenContent cs
  flattenParenContent (Operator n ocs : cs)     = Operator n (flattenParenContent ocs) : flattenParenContent cs
  flattenParenContent (c : cs)                  = c : flattenParenContent cs
  flattenParenContent []                        = []

  -- Condense adjacent StringContents together.
  -- Use this before seperating on ,, and not after
  globSCs :: [Content] -> [Content]
  globSCs (StringContent s : StringContent s2 : xs) = globSCs (StringContent (s `append` s2) : xs)
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
  eliminateEmptySCs (StringContent s : cs) | s == pack "" = eliminateEmptySCs cs
  eliminateEmptySCs (Operator n cs : rest)  = Operator n (eliminateEmptySCs cs) : eliminateEmptySCs rest
  eliminateEmptySCs (c : cs)                = c : eliminateEmptySCs cs
  eliminateEmptySCs []                      = []

  -- Convert back into a string
  contentToString :: Content -> ByteString
  contentToString (StringContent s) = s
  contentToString (Operator name cs) | shouldInfix name  = join (" " ++ init (tail (unpack name)) ++ " ")  innards
                                     | shouldMixfix name = join " " $ intermix (seperateMixfix name) innards
                                     | otherwise         = name `append` pack "(" `append` join ",," innards `append` pack ")"
    where innards = map contentToString cs

  shouldInfix :: ByteString -> Bool
  shouldInfix s = case B.uncons s of
                    Just ('_',cs) -> B.last cs == '_' && '_' `notIn` B.init cs
                    _             -> False
    where x `notIn` xs = not $ x `B.elem` xs

  shouldMixfix :: ByteString -> Bool
  shouldMixfix s = '_' `B.elem` s

  seperateMixfix :: ByteString -> [ByteString]
  seperateMixfix s = "_" `split` (deleteAll '`' s)



  -- Intermix two string lists. The first argument should be of size one greater than the second
  intermix :: [a] -> [a] -> [a]
  intermix (l:ls) (r:rs) = l : r : intermix ls rs
  intermix [left] [] = [left]
  intermix _ _ =  error "Output contains the wrong number of arguments for a mixfix operator"

  -- Do the whole shebang
  makeInfix :: ByteString -> ByteString
  makeInfix s = case runParser parseContentsTop 0 "" s of
                  Left err -> error $ show err
                  Right cs -> join " " . map contentToString $ postProcess cs


