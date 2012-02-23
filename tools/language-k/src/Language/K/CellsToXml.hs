{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.CellsToXml
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- This module provides an Attoparsec parser for transforming the output of
-- the KMaude tool into valid XML.  See 'cellsToXml'.
-----------------------------------------------------------------------------

module Language.K.CellsToXml
    (
    -- * Run the parser
      cellsToXml
    , cellsToXml'
    -- * Parser components
    , koutput
    , cell
    , insides
    , content
    , startTag
    , endTag
    ) where

import Control.Applicative ((<|>), (<$>))
import Data.Attoparsec.Text
import Data.Attoparsec.Extra.Text
import Data.Text (Text)
import qualified Data.Text as T
import Data.Char (isAlphaNum)

-- | Transforms output from the K Maude tool (without cruft like the Maude
-- header) into valid XML.  This transformation consists of three parts:
--
-- * Removing the spaces around cell tags
--
-- * Wrapping everything in a \<root\> element
--
-- * Escaping characters like @\<@, @\>@, and @&@
--
-- >>> cellsToXml "< k > foo </ k >"
-- Done "" "<root><k> foo </k></root>"
-- >>> cellsToXml "< env > 0 |-> 42 </ env >"
-- Done "" "<root><env> 0 |-&lt; 42 </env></root>"
--
-- TODO: use parseOnly here.
cellsToXml :: Text -> Result Text
cellsToXml s = feed (parse koutput s) T.empty

-- | Same as 'cellsToXml' but lifted to 'Either'.
cellsToXml' :: Text -> Either String Text
cellsToXml' = eitherResult . cellsToXml

-- | Parses several cells that make up K output.  The result is wrapped in a
-- \<root\> element because valid XML documents have only one root.
koutput :: Parser Text
koutput = xmlify "root" <$> many1 (spaces >> cell)

-- | Parses a single cell and converts it to valid XML.
cell :: Parser Text
cell = do
    name <- startTag
    insides <- manyTill insides (endTag name)
    return $ xmlify name insides

-- | Parses the insides of a cell: either another cell or content.
insides :: Parser Text
insides = cell <|> content

-- | Parses data that is not structural/markup.  This parser also does XML
-- escaping in content.
content :: Parser Text
content = takeWhile1 (not . needsEscape) <|> escape <$> satisfy needsEscape

-- | Parses a cell start tag such as \"\< foo \>\".
startTag :: Parser Text
startTag = do
    char '<'
    skipSpace1
    name <- takeWhile1 isAlphaNum
    skipSpace1
    char '>'
    return name

-- | Parses a cell end tag with the given name, such as \"\</ foo \>\".
endTag :: Text -> Parser ()
endTag tag = do
    string "</"
    skipSpace1
    string tag
    skipSpace1
    char '>'
    return ()

-- | Wraps a list of 'Text's in XML tags with the given name.
xmlify :: Text -> [Text] -> Text
xmlify tag contents = T.concat $
    ["<", tag, ">"] ++ contents ++ ["</", tag, ">"]

-- | Checks if the given word needs to be escaped in XML.  Only @>@, @<@, and
-- @&@ really need to be escaped.
needsEscape :: Char -> Bool
needsEscape w =
       w == '>'
    || w == '<'
    || w == '&'

-- | Converts an escape character to the appropriate character entity. 
escape :: Char -> Text
escape '>' = "&gt;"
escape '<' = "&lt;"
escape '&' = "&amp;"
