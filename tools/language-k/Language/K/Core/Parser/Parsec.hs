{-# LANGUAGE FlexibleContexts, Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Core.Parser.Parsec
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- A Parsec parser for K Core.
-----------------------------------------------------------------------------

module Language.K.Core.Parser.Parsec where

import Control.Applicative ((<$>))
import Text.Parsec

import Language.K.Core.Syntax
import Internal.Lexer

parseK :: String -> Either ParseError K
parseK = parse kterm ""

-- | Reduce clutter while still keeping the types generic.
type Parser a = (Stream s m Char) => ParsecT s u m a

-- | Parse a K term
kterm :: Parser K
kterm = kapp

-- | Parse a K application: KLabel(K1,,K2)
kapp :: Parser K
kapp = do
    kl <- klabel
    argv <- parens klist
    return $ KApp kl argv

klist :: Parser [K]
klist = kempty <|> (kterm `sepBy` (symbol ",,"))

-- | Parse the K identity element
kempty :: Parser [K]
kempty = string ".List{K}" >> return []

{- KLabels -}

-- | Parse a KLabel
klabel :: Parser KLabel
klabel = genklabel <|> kbuiltin

-- | Parse generated K label: 'Foo___
genklabel :: Parser KLabel
genklabel = KLabel <$> (char '\'' >> many1 klabelpart)

-- | Parse part of a K label (an '_' arg or syntax)
klabelpart :: Parser KLabelPart
klabelpart = syntax <|> hole
    where syntax = Syntax <$> maudeIdentifier
          hole = char '_' >> return Hole

-- TODO: I've quickly modified the builtin parsers below to handle the new
-- syntax for builtins:
-- # 42 instead of #Int 42
-- These modifications may not be entirely correct and require more testing.

-- | Parse a K builtin
kbuiltin :: Parser KLabel
kbuiltin = do
    symbol "#"
    try kbool <|> kint <|> kid <|> kstring
--    try kid <|> knat <|> kint <|> kstring <|> kbool

-- | Parse an Id builtin: Id x
kid :: Parser KLabel
kid = do
--    symbol "Id"
    id <- many1 alphaNum
    return (KId id)

-- | Parse a Nat builtin: Nat 42
knat :: Parser KLabel
knat = do
    symbol "Nat"
    i <- integer
    return (KNat i)

-- | Parse an Int builtin: Int 42
kint :: Parser KLabel
kint = do
--    symbol "Int"
    i <- integer
    return (KInt i)

-- | Parse a String builtin: String "hello"
kstring :: Parser KLabel
kstring = do
--    symbol "String"
    s <- stringLiteral
    return (KString s)

-- | Parse a Bool builtin: Bool true or Bool false
kbool :: Parser KLabel
kbool = do
--    symbol "Bool"
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
