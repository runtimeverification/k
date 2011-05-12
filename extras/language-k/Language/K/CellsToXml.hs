{-# LANGUAGE OverloadedStrings #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.CellsToXml
-- Copyright   :  (c) David Lazar, 2011
-- License     :  BSD3
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  non-portable
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
import Data.Attoparsec.Char8
import Data.Attoparsec.Extra
import Data.ByteString.Char8 (ByteString)
import qualified Data.ByteString.Char8 as B
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
cellsToXml :: ByteString -> Result ByteString
cellsToXml s = feed (parse koutput s) B.empty

-- | Same as 'cellsToXml' but lifted to 'Either'.
cellsToXml' :: ByteString -> Either String ByteString
cellsToXml' = eitherResult . cellsToXml

-- | Parses several cells that make up K output.  The result is wrapped in a
-- \<root\> element because valid XML documents have only one root.
koutput :: Parser ByteString
koutput = xmlify "root" <$> many (spaces >> cell)

-- | Parses a single cell and converts it to valid XML.
cell :: Parser ByteString
cell = do
    name <- startTag
    insides <- manyTill insides (endTag name)
    return $ xmlify name insides

-- | Parses the insides of a cell: either another cell or content.
insides :: Parser ByteString
insides = cell <|> content

-- | Parses data that is not structural/markup.  This parser also does XML
-- escaping in content.
content :: Parser ByteString
content = takeWhile1 (not . needsEscape) <|> escape <$> satisfy needsEscape

-- | Parses a cell start tag such as \"\< foo \>\".
startTag :: Parser ByteString
startTag = do
    char '<'
    spaces
    name <- takeWhile1 isAlphaNum
    spaces
    char '>'
    return name

-- | Parses a cell end tag with the given name, such as \"\</ foo \>\".
endTag :: ByteString -> Parser ()
endTag tag = do
    string "</"
    spaces
    string tag
    spaces
    char '>'
    return ()

-- | Wraps a list of 'ByteString's in XML tags with the given name.
xmlify :: ByteString -> [ByteString] -> ByteString
xmlify tag contents = B.concat $
    ["<", tag, ">"] ++ contents ++ ["</", tag, ">"]

-- | Checks if the given word needs to be escaped in XML.  Only @>@, @<@, and
-- @&@ really need to be escaped.
needsEscape :: Char -> Bool
needsEscape w =
       w == '>'
    || w == '<'
    || w == '&'

-- | Converts an escape character to the appropriate character entity. 
escape :: Char -> ByteString
escape '>' = "&gt;"
escape '<' = "&lt;"
escape '&' = "&amp;"
