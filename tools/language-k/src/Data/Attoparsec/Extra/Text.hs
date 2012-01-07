{-# LANGUAGE OverloadedStrings #-}
module Data.Attoparsec.Extra.Text where

import Data.Attoparsec.Text
import Data.Text (Text)

-- | @between open close p@ parses @open@, followed by @p@ and @close@.
-- Returns the value returned by @p@.
between :: Parser open -> Parser close -> Parser a -> Parser a
between open close p = do { open; x <- p; close; return x }

-- | Parse a string and skip trailing whitespace.
symbol :: Text -> Parser Text
symbol s = do { r <- string s; spaces; return r }

-- | @parens p@ parses @p@ enclosed in parenthesis
parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

-- | Alias for Attoparsec's 'skipSpace'.
spaces :: Parser ()
spaces = skipSpace

-- | Skip over whitespace, consuming at least one space.
skipSpace1 :: Parser ()
skipSpace1 = space >> skipSpace
