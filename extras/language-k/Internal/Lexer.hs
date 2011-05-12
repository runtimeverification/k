{-# LANGUAGE FlexibleContexts #-}
module Internal.Lexer
    ( Internal.Lexer.identifier
    , Internal.Lexer.integer
    , Internal.Lexer.parens
    , Internal.Lexer.stringLiteral
    , Internal.Lexer.symbol
    ) where

import Text.Parsec
import Text.Parsec.Token 
    ( GenLanguageDef(..)
    , GenTokenParser(..)
    , makeTokenParser
    )
import qualified Text.Parsec.Token as P

-- | This is a minimal token definition for Haskell style languages. It
-- defines the style of comments, valid identifiers and case
-- sensitivity. It does not define any reserved words or operators.
haskellStyle :: (Stream s m Char) => GenLanguageDef s u m
haskellStyle = LanguageDef
    { commentStart    = "{-"
    , commentEnd      = "-}"
    , commentLine     = "--"
    , nestedComments  = True
    , identStart      = letter
    , identLetter	  = alphaNum <|> oneOf "_'"
    , opStart	      = opLetter haskellStyle
    , opLetter	      = oneOf ":!#$%&*+./<=>?@\\^|-~"
    , reservedOpNames = []
    , reservedNames   = []
    , caseSensitive   = True
    }

lexer :: (Stream s m Char) => GenTokenParser s u m
lexer = makeTokenParser haskellStyle

identifier :: (Stream s m Char) => ParsecT s u m String
identifier = P.identifier lexer

integer :: (Stream s m Char) => ParsecT s u m Integer
integer = P.integer lexer

parens :: (Stream s m Char) => ParsecT s u m a -> ParsecT s u m a
parens = P.parens lexer

stringLiteral :: (Stream s m Char) => ParsecT s u m String
stringLiteral = P.stringLiteral lexer

symbol :: (Stream s m Char) => String -> ParsecT s u m String
symbol = P.symbol lexer
