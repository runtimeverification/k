{-# LANGUAGE FlexibleContexts, Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K
-- Copyright   :  (c) David Lazar, 2011
-- License     :  BSD3
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A small, incomplete parser for low-level K.
-----------------------------------------------------------------------------

module Language.K where

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
    (label, argc) <- klabel
    argv <- parens (kterm `sepBy` (symbol ",,"))
    proceed label argc argv
    where proceed label argc argv
              | argc == 0 = return label
              | argc /= length argv = fail "unexpected number of arguments"
              | otherwise = return $ label ++ " " ++ parenthesize argv

{- KLabels -}

-- | A KLabel is its name and its number of arguments
type KLabel = (String, Int)

-- | Parse a KLabel
klabel :: Parser KLabel
klabel = genklabel <|> kbuiltin

-- | Parse generated K label: 'Foo___
genklabel :: Parser KLabel
genklabel = do
    char '\''
    name <- maudeIdentifier
    argc <- length <$> many (char '_')
    return (name, argc)

-- | Parse a K builtin
kbuiltin :: Parser KLabel
kbuiltin = flip (,) 0 <$> (kint <|> kstring)

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
maudeIdentifier = many maudeIdChar

maudeIdChar :: Parser Char
maudeIdChar = noneOf ("`_ " ++ maudeIdSpecialChars) <|> maudeIdEscape

maudeIdEscape :: Parser Char
maudeIdEscape = char '`' >> oneOf maudeIdSpecialChars

-- | 3.1: The characters ‘{’, ‘}’, ‘(’, ‘)’, ‘[’, ‘]’ and ‘,’ are special, in
-- that they break a sequence of characters into several identifiers.
maudeIdSpecialChars :: String
maudeIdSpecialChars = "{}()[],"

{- Utilities -}

-- | ["x", "y", "z"] -> "(x) (y) (z)"
parenthesize :: [String] -> String
parenthesize = unwords . map (\x -> "(" ++ x ++ ")")
