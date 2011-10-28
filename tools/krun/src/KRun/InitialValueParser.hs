{-# LANGUAGE OverloadedStrings #-}
module KRun.InitialValueParser where

import Control.Applicative
import Data.Either
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Attoparsec.Text
import KRun.Types

parseKeyVals :: [Text] -> Either String (Map Text Kast)
parseKeyVals txts = case partitionEithers $ map (parseOnly keyVal) txts of
    ([], rs) -> Right $ Map.fromList $ map (\(k, v) -> (k, Kast v)) rs
    ((x:xs), _) -> Left x

keyVal = do
    key <- takeWhile1 (/= '=')
    char '='
    val <- try kmap <|> klist
    return (key, val)

kmap = do
    items <- many1 $ do
        skipSpace
        i <- mapItem
        skipSpace
        return i
    let map = T.intercalate "," $ items ++ ["(.).Map"]
    return $ T.concat ["wmap(__(", map, "))(.List{K})"]

mapItem = do
    id <- takeWhile1 (\x -> x /= ' ' && x /= '|')
    skipSpace
    string "|->"
    skipSpace
    k <- takeWhile1 (/= ' ')
    return $ T.concat ["_|->_(# #id \"", id, "\"(.List{K}),# ", k, "(.List{K}))"]

klist = do
    items <- many1 $ do
        skipSpace
        i <- listItem
        skipSpace
        return i
    let list = T.intercalate "," $ items ++ ["(.).List"]
    return $ T.concat ["wlist(__(", list, "))(.List{K})"]

-- TODO: assuming lists/bags of numbers for now.
-- Strings or chars with ')' in them will break.
listItem = do
    ctor <- string "ListItem"
    char '('
    item <- takeWhile1 (/= ')')
    char ')'
    return $ T.concat [ctor, "(# ", item, "(.List{K}))"]
