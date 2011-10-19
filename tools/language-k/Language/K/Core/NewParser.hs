{-# LANGUAGE OverloadedStrings #-}
module Language.K.Core.NewParser where

import Control.Applicative ((<$>))
import qualified Data.Map as Map
import Language.K.Core.Syntax
import Internal.Lexer
import Text.Parsec
import Text.Parsec.String

-- | Parse a K term
k :: Parser K
k = try kra <|> kApp

kra :: Parser K
kra = emptyK -- <|> TODO

emptyK :: Parser K
emptyK = do
    string "(.).K"
    return $ Kra []

-- | Parse a K application: KLabel(K1,,K2)
kApp :: Parser K
kApp = do
    kl <- kLabel
    argv <- parens listK
    return $ KApp kl argv

listK :: Parser [K]
listK = emptyListK <|> (k `sepBy` (symbol ",,"))
      <?> "list K"

-- | Parse the empty list of K
emptyListK :: Parser [K]
emptyListK = do
    string ".List{K}"
    return []
    <?> "empty list of K"

kBag :: Parser KBag
kBag = emptyKBag <|> (KBag <$> bagItem `endBy1` spaces)

emptyKBag :: Parser KBag
emptyKBag = do
    string "(.).Bag"
    return $ KBag []

-- TODO: why is the try below necessary?
bagItem :: Parser BagItem
bagItem = try cellItem <|> bagItem'

bagItem' :: Parser BagItem
bagItem' = do
    string "BagItem"
    k <- parens k
    return $ BagItem k

cellItem :: Parser BagItem
cellItem = do
    name <- startTag
    content <- cellContent
    endTag name
    return $ CellItem name content

cellContent :: Parser CellContent
cellContent = try mapContent <|> try bagContent <|> kContent

kContent :: Parser CellContent
kContent = KContent <$> k

bagContent :: Parser CellContent
bagContent = BagContent <$> kBag

mapContent :: Parser CellContent
mapContent = MapContent <$> kMap

startTag :: Parser String
startTag = do
    char '<'
    spaces
    name <- many1 alphaNum
    spaces
    char '>'
    spaces
    return name

endTag :: String -> Parser ()
endTag tag = do
    spaces
    string "</"
    spaces
    string tag
    spaces
    char '>'
    return ()

-- TODO: Sets and Lists

kMap :: Parser KMap
kMap = emptyKMap <|> KMap . Map.fromList <$> mapItem `endBy1` spaces

emptyKMap :: Parser KMap
emptyKMap = do
    string "(.).Map"
    return $ KMap Map.empty

mapItem :: Parser (K, K)
mapItem = do
    k1 <- k
    spaces
    string "|->"
    spaces
    k2 <- k
    return (k1, k2)


-- | Parse a KLabel
kLabel :: Parser KLabel
kLabel = quotedKLabel <|> kBuiltin
       <?> "K label"

-- | Parse "quoted" K label: 'Foo___
quotedKLabel :: Parser KLabel
quotedKLabel = KLabel <$> (char '\'' >> many1 kLabelPart)
             <?> "quoted K label"

-- | Parse part of a K label (an '_' arg or syntax)
kLabelPart :: Parser KLabelPart
kLabelPart = syntax <|> hole
    where syntax = Syntax <$> maudeIdentifier
          hole = char '_' >> return Hole

-- | Parse a K builtin
kBuiltin :: Parser KLabel
kBuiltin = do
    symbol "#"
    try kBool <|> kInt <|> kId <|> kString
    <?> "K builtin"

-- | Parse an Id builtin: Id x
kId :: Parser KLabel
kId = do
    symbol "#id "
    id <- stringLiteral
    return (KId id)

-- | Parse an integer literal: 42
kInt :: Parser KLabel
kInt = do
    i <- integer
    return (KInt i)

-- | Parse a String literal: "hello"
kString :: Parser KLabel
kString = do
    s <- stringLiteral
    return (KString s)

-- | Parse a boolean literal: true
kBool :: Parser KLabel
kBool = do
    b <- (symbol "true" >> return True) <|> (symbol "false" >> return False)
    return (KBool b)

{- Maude identifiers -}

-- | Note that this does not capture all Maude identifiers since, for K, we
-- assume identifiers will not contain '_'  and that '`' will not be used to
-- escape spaces.
maudeIdentifier :: Parser String
maudeIdentifier = many1 maudeIdChar

maudeIdChar :: Parser Char
maudeIdChar = noneOf ("`_ " ++ maudeIdSpecialChars) <|> maudeIdEscape

maudeIdEscape :: Parser Char
maudeIdEscape = char '`' >> oneOf maudeIdSpecialChars

-- | 3.1: The characters '{', '}', '(', ')', '[', ']' and ',' are special,
-- in that they break a sequence of characters into several identifiers.
maudeIdSpecialChars :: String
maudeIdSpecialChars = "{}()[],"
