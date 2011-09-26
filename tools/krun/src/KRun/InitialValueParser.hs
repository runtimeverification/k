{-# LANGUAGE OverloadedStrings #-}
module KRun.InitialValueParser where

import Control.Applicative
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as T
import Data.Attoparsec.Text
import KRun.Types

parseKeyVals :: [Text] -> Either String (Map Text Kast)
parseKeyVals txts = do
    keyVals <- mapM (parseOnly keyVal) txts
    return $ Map.fromList $ map (\(k, v) -> (k, Kast v)) keyVals

keyVal = do
    key <- takeWhile1 (/= '=')
    char '='
    val <- listOrBag
    return (key, val)

listOrBag = do
    items <- many1 $ do
        skipSpace
        i <- listOrBagItem
        skipSpace
        return i
    return $ T.intercalate " " items

-- TODO: assuming lists/bags of numbers for now.
-- Strings or chars with ')' in them will break.
listOrBagItem = do
    ctor <- string "ListItem" <|> string "BagItem"
    char '('
    item <- takeWhile1 (/= ')')
    char ')'
    return $ T.concat [ctor, "(# ", item, "(.List{K}))"]
