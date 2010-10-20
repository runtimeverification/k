-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Yaml.YamlLight
-- Copyright   :  Michael Ilseman (c) 2010
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  michael <dot> ilseman <at> gmail <dot> com
-- Stability   :  provisional
-- Portability :  portable
--
-- A light-weight wrapper with utility functions around HsSyck

{-# LANGUAGE OverloadedStrings #-}

module Data.Yaml.YamlLight
  ( -- * YamlLight data type
    YamlLight(..)
    -- * YamlLight versions of Syck functions
  , parseYaml, parseYamlFile, parseYamlBytes
    -- * YamlLight utility functions
  , fromYamlNode, lookupYL, lookupYLWith
    -- ** Extractors
  , unSeq, unMap, unStr
  ) where
  import Control.Applicative
  import Data.Data
  import Data.List
  import qualified Data.Yaml.Syck as Syck
  import qualified Data.Map as Map
  import qualified Data.ByteString as ByteString

  data YamlLight = YMap (Map.Map YamlLight YamlLight)
                 | YSeq [YamlLight]
                 | YStr ByteString.ByteString
                 | YNil
    deriving (Show, Ord, Eq)

  convert :: (a -> Syck.YamlNode) -> (a -> YamlLight)
  convert f = fromYamlNode . f

  convertIO :: (a -> IO Syck.YamlNode) -> (a -> IO YamlLight)
  convertIO f yn = fromYamlNode <$> f yn

  -- | Parse a regular Haskell string
  parseYaml :: String -> IO YamlLight
  parseYaml = convertIO Syck.parseYaml

  -- | Given a file name, parse contents of file
  parseYamlFile :: String -> IO YamlLight
  parseYamlFile = convertIO Syck.parseYamlFile

  -- | Parse a ByteString buffer (this is faster)
  parseYamlBytes :: ByteString.ByteString -> IO YamlLight
  parseYamlBytes = convertIO Syck.parseYamlBytes

  -- | Convert a Syck YamlNode to a YamlLight
  fromYamlNode :: Syck.YamlNode -> YamlLight
  fromYamlNode = yamlElemToLight . Syck.n_elem

  yamlElemToLight :: Syck.YamlElem -> YamlLight
  yamlElemToLight (Syck.EMap ms)  = YMap . Map.fromList . map (\(a,b) -> (fromYamlNode a, fromYamlNode b)) $ ms
  yamlElemToLight (Syck.ESeq s)   = YSeq $ map fromYamlNode s
  yamlElemToLight (Syck.EStr buf) = YStr buf
  yamlElemToLight (Syck.ENil)     = YNil

  -- | Lookup the key's corresponding value in a Map. Returns Nothing if the YamlLight is not a map, or if
  -- the key is not found
  lookupYL :: YamlLight -> YamlLight -> Maybe YamlLight
  lookupYL key (YMap m) = Map.lookup key m
  lookupYL _ _          = Nothing

  -- | General form of lookup. Will return the first element that satisfies predicate p, otherwise Nothing
  lookupYLWith :: (YamlLight -> Bool) -> YamlLight -> Maybe YamlLight
  lookupYLWith p (YMap m) = snd <$> (find (p . fst) $ Map.toList m)
  lookupYLWith _ _        = Nothing

  -- | Get the contents of a sequence
  unSeq :: YamlLight -> Maybe [YamlLight]
  unSeq (YSeq s) = Just s
  unSeq _       = Nothing

  -- | Get the contents of a map
  unMap :: YamlLight -> Maybe (Map.Map YamlLight YamlLight)
  unMap (YMap m) = Just m
  unMap _       = Nothing

  -- | Get the contents of a string
  unStr :: YamlLight -> Maybe ByteString.ByteString
  unStr (YStr s) = Just s
  unStr _       = Nothing


