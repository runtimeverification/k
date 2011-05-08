{-# LANGUAGE FlexibleContexts, Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Parser.Parsec
-- Copyright   :  (c) David Lazar, 2011
-- License     :  BSD3
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A small, incomplete Parsec parser for low-level K.
-----------------------------------------------------------------------------

module Language.K.Parser.Parsec where

import Control.Applicative ((<$>))
import Text.Parsec

import Internal.Lexer

-- | Reduce clutter while still keeping the types generic.
type Parser a = (Stream s m Char) => ParsecT s u m a

-- | Parse a K term
kterm :: Parser String
kterm = kempty <|> kapp

-- | Parse the K identity element
kempty :: Parser String
kempty = string ".List{K}"

-- | Parse a K application: KLabel(K1,,K2)
kapp :: Parser String
kapp = do
    kl <- klabel
    argv <- parens (kterm `sepBy` (symbol ",,"))
    return . unwords $ zipSyntax kl argv

-- | Combine a KLabel and a list of arguments to form the original
-- abstract syntax.
zipSyntax (Syntax s : xs) as = s : zipSyntax xs as
zipSyntax (Arg : xs) (a : as) = ("(" ++ a ++ ")") : zipSyntax xs as
zipSyntax _ _ = []

{- KLabels -}

data KLabelPart = Syntax String | Arg
    deriving (Eq, Show)

type KLabel = [KLabelPart]

-- | Parse a KLabel
klabel :: Parser KLabel
klabel = genklabel <|> kbuiltin

-- | Parse generated K label: 'Foo___
genklabel :: Parser KLabel
genklabel = char '\'' >> many1 klabelpart

-- | Parse part of a K label (an '_' arg or syntax)
klabelpart :: Parser KLabelPart
klabelpart = syntax <|> arg
    where syntax = Syntax <$> maudeIdentifier
          arg = char '_' >> return Arg

-- | Parse a K builtin
kbuiltin :: Parser KLabel
kbuiltin = (:[]) . Syntax <$> (try kid <|> kint <|> kstring)

-- | Parse an Id builtin: Id x
kid :: Parser String
kid = do
    symbol "Id"
    id <- many1 alphaNum
    return id

-- | Parse an Int builtin: Int 42
kint :: Parser String
kint = do
    symbol "Int"
    i <- integer
    return (show i)

-- | Parse a String builtin: String "hello"
kstring :: Parser String
kstring = do
    symbol "String"
    s <- stringLiteral
    return (show s)

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
