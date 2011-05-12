{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Parser.Attoparsec
-- Copyright   :  (c) David Lazar, 2011
-- License     :  BSD3
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
--
-- A small, incomplete Attoparsec parser for low-level K.
-----------------------------------------------------------------------------

module Language.K.Core.Parser.Attoparsec where

import Control.Applicative ((<|>), (<$>))
import Data.Attoparsec.Char8
import Data.Attoparsec.Extra
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B
import Data.ByteString.Builder
import qualified Data.String
import Prelude hiding (unwords, takeWhile)

-- | Parse a K term
kterm :: Parser Builder
kterm = kempty <|> kapp

-- | Parse the K identity element
kempty :: Parser Builder
kempty = fromByteString <$> string ".List{K}"

-- | Parse a K application: KLabel(K1,,K2)
kapp :: Parser Builder
kapp = do
    (label, argc) <- klabel
    argv <- parens (kterm `sepBy` (symbol ",,"))
    proceed label argc argv
    where proceed label argc argv
              | argc == 0 = return label
              | argc /= length argv = fail "unexpected number of arguments"
              | otherwise = return $ label <> " " <> parenthesize argv

{- KLabels -}

-- | A KLabel is its name and its number of arguments
type KLabel = (Builder, Int)

-- | Parse a KLabel
klabel = genklabel <|> kbuiltin

-- | Parse generated K label: 'Foo___
-- TODO: this does not capture all K labels, only "generated" ones.
genklabel :: Parser KLabel
genklabel = do
    char '\''
    name <- maudeIdentifier
    argc <- B.length <$> takeWhile (== '_')
    return (name, argc)

-- | Parse a K builtin: Int 42(.List{K})
kbuiltin :: Parser KLabel
kbuiltin = flip (,) 0 <$> (kint <|> kstring)

-- | Parse an Int builtin: Int 42
kint :: Parser Builder
kint = do
    string "Int"
    spaces
    i <- signed decimal
    return $ fromString (show i)

-- | Parse a String builtin: String "hello"
kstring :: Parser Builder
kstring = do
    string "String"
    spaces
    char '"'
    content <- many stringBits
    char '"'
    return $ "\"" <> mconcat content <> "\""
    where stringBits = fromByteString <$> takeWhile1 (not . special) <|> escape
          special c  = c == '\\' || c == '"'
          escape = do 
              char '\\'
              -- HACK: we assume strings are escaped properly, so eat one
              -- character past the slash and move on.
              c <- anyChar
              return ("\\" <> fromChar c)

{- Maude identifiers -}

-- | Note that this does not capture all Maude identifiers since, for K, we
-- assume identifiers will not contain '_'  and that '`' will not be used to
-- escape spaces.
maudeIdentifier :: Parser Builder
maudeIdentifier = mconcat <$> many idBits
    where idBits  = fromByteString <$> takeWhile1 (not . special) <|> escape
          special = inClass ("`_ " ++ escapeChars)
          escape  = char '`' >> fromChar <$> satisfy (inClass escapeChars)
          escapeChars = "{}()[],"

{- Utilities -}

-- | ["x", "y", "z"] -> "(x) (y) (z)"
parenthesize :: (Monoid a, Data.String.IsString a) => [a] -> a
parenthesize = unwords . map (\x -> "(" <> x <> ")")
