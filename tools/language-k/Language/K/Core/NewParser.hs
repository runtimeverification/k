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
k = try kra <|> try kApp <|> freezerVar

optParens p = parens p <|> p

kra :: Parser K
kra = emptyK <|> (Kra <$> kApp `sepBy2` (symbol "~>"))

emptyK :: Parser K
emptyK = do
    string "." <|> string "(.).K"
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

freezerVar :: Parser K
freezerVar = do
    string "var{K}"
    varName <- parens stringLiteral
    return $ FreezerVar varName

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
cellContent = try mapContent <|> try bagContent <|> try listContent <|> try setContent <|> kContent

kContent :: Parser CellContent
kContent = KContent <$> k

bagContent :: Parser CellContent
bagContent = BagContent <$> kBag

listContent :: Parser CellContent
listContent = ListContent <$> kList

setContent :: Parser CellContent
setContent = SetContent <$> kSet

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

kSet :: Parser KSet
kSet = emptyKSet <|> KSet <$> setItem `endBy1` spaces

emptyKSet :: Parser KSet
emptyKSet = do
    string "(.).Set"
    return $ KSet []

setItem :: Parser K
setItem = do
    string "SetItem"
    k <- parens k
    return k

kList :: Parser KList
kList = emptyKList <|> KList <$> listItem `endBy1` spaces

emptyKList :: Parser KList
emptyKList = do
    string "(.).List"
    return $ KList []

listItem :: Parser ListItem
listItem = listItem' <|> try buffer <|> try istream <|> ostream

listItem' :: Parser ListItem
listItem' = do
    string "ListItem"
    k <- parens k
    return $ ListItem k

buffer :: Parser ListItem
buffer = do
    string "#buffer"
    k <- parens k
    return $ Buffer k

istream :: Parser ListItem
istream = do
    string "#istream"
    i <- parens integer
    return $ IStream i

ostream :: Parser ListItem
ostream = do
    string "#ostream"
    i <- parens integer
    return $ OStream i

kMap :: Parser KMap
kMap = emptyKMap <|> KMap . Map.fromList <$> mapItem `endBy1` spaces

emptyKMap :: Parser KMap
emptyKMap = do
    string "(.).Map" <|> string "."
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
kLabel = quotedKLabel <|> try kBuiltin <|> try freezer <|> try freezerMap <|> wmap
       <?> "K label"

freezer :: Parser KLabel
freezer = do
    string "freezer"
    k <- parens k
    return $ Freezer k

freezerMap :: Parser KLabel
freezerMap = do
    FreezerVar var <- freezerVar
    string "<-"
    return $ FreezerMap var

wmap :: Parser KLabel
wmap = do
    string "wmap"
    spaces
    kmap <- kMap
    return $ WMap kmap

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

maudeIdentifier :: Parser String
maudeIdentifier = concat <$> many1 maudeIdPart

maudeIdPart :: Parser String
maudeIdPart = (show <$> stringLiteral) <|> ((:[]) <$> maudeIdChar)

maudeIdChar :: Parser Char
maudeIdChar = noneOf ("`_ " ++ maudeIdSpecialChars) <|> maudeIdEscape

maudeIdEscape :: Parser Char
maudeIdEscape = char '`' >> (oneOf maudeIdSpecialChars <|> return ' ')

-- | 3.1: The characters '{', '}', '(', ')', '[', ']' and ',' are special,
-- in that they break a sequence of characters into several identifiers.
maudeIdSpecialChars :: String
maudeIdSpecialChars = "{}()[],"

-- TODO: move this?
sepBy2 p sep = do { x <- p
                  ; xs <- many1 (sep >> p)
                  ; return (x:xs)
                  }
