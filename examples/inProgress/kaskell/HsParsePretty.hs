{-
  Module for running the haskell parser, parsing the AST produced, and pretty printing it
  When invoked on the shell, use the form "runhaskell HsParsePretty.hs <module-name>"
  If no module name is provided, this module (HsParsePretty) is used.
 -}

module HsParsePretty where
  import Language.Haskell.Exts.Parser hiding (parse)
  import Language.Haskell.Exts.Pretty
  import System.Environment
  import Text.PrettyPrint.ANSI.Leijen as PP hiding (char, string, space)
  import Text.ParserCombinators.Parsec
  import Control.Monad

  -- Parse the string representing the Ast
  -- Structs, such as tuples, lists, or just parens, consist of the insides, surrounded by two characters
  data Ast = Contents String | Struct Char [Ast] Char | Seq [Ast] | Str String | Char String | None
             deriving (Show,Eq)

  contentsP :: Parser Ast
  contentsP = try (space >> return None) <|> (many1 (noneOf "({[\"\',]})") >>= return . Contents)

  stringP :: Parser Ast
  stringP = between (char '\"') (char '\"') innards >>= return . Str . concat
    where innards = many $ try (string "\\\"") <|> (noneOf "\"" >>= return . return)

  charP :: Parser Ast
  charP = between (char '\'') (char '\'') innards >>= return . Char
    where innards = try (string "\\\'") <|> (noneOf "\'" >>= return . return)

  structP :: Parser Ast
  structP = do l <- oneOf "({["
               innards <- astP `sepBy` char ','
               r <- oneOf "]})"
               return $ Struct l innards r

  seqP = do seq <- many singleAstP
            case length seq of
              0 -> return None
              1 -> return (head seq)
              _ -> return (Seq seq)

  singleAstP :: Parser Ast
  singleAstP = contentsP <|> stringP <|> charP <|> structP

  astP :: Parser Ast
  astP = seqP

  -- Pretty print the ast
  ppAst :: Ast -> Doc
  ppAst (Contents s) = text s
  ppAst (Seq asts) = head docs <> (encloseSep empty empty empty $ tail docs)
    where docs = map ppAst $ filter (\x -> x /= None) asts
  ppAst None = text ""
  ppAst (Str str) = ppChar '\"' <> text str <> ppChar '\"'
  ppAst (Char str) = ppChar '\'' <> text str <> ppChar '\''
  ppAst (Struct l asts r) = encloseSep (ppChar l) (ppChar r) comma (map ppAst asts)

  ppChar = text . return

  -- By default, loads and runs on this modlue (Parse.hs). If an argument is passed, then that module is used
  main :: IO ()
  main = do args <- getArgs
            fname <- if length args == 0 then getProgName else return (head args)
            contents <- readFile fname
            let parseM = case parseModule contents of
                          ParseOk r -> r
                          ParseFailed loc s -> error s
            putStrLn . prettyPrint $ parseM
            putStrLn "\nParses as:"
            putStrLn . show $ parseM
            putStrLn "\nParsecs as:"
            let parsecOut = case parse astP "" (show parseM) of Right a -> a
            parseTest astP $ show parseM
            putStrLn "\nPretty:"
            putDoc . ppAst $ parsecOut

