{-# LANGUAGE DeriveDataTypeable #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Core.Syntax
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- Data types describing the abstract syntax of K Core.
-----------------------------------------------------------------------------

module Language.K.Core.Syntax where

import Data.Data
import Data.Map (Map)

data K
    = KApp KLabel [K]
    | Kra [K]
    deriving (Eq, Ord, Show, Data, Typeable)

data KLabel
    = KLabel [KLabelPart]
    | KNat Integer
    | KInt Integer
    | KBool Bool
    | KString String
    | KId String
    deriving (Eq, Ord, Show, Data, Typeable)

data KLabelPart
    = Syntax String
    | Hole
    deriving (Eq, Ord, Show, Data, Typeable)

data KList = KList [K]
    deriving (Eq, Ord, Show, Data, Typeable)

data KBag = KBag [BagItem]
    deriving (Eq, Ord, Show, Data, Typeable)

data BagItem
    = BagItem K
    | CellItem
        { cellItemLabel :: String
        , cellItemContent :: CellContent
        }
    deriving (Eq, Ord, Show, Data, Typeable)

data KSet = KSet [K]
    deriving (Eq, Ord, Show, Data, Typeable)

data KMap = KMap (Map K K)
    deriving (Eq, Ord, Show, Data, Typeable)

data CellContent
    = KContent K
    | ListContent KList
    | BagContent KBag
    | SetContent KSet
    | MapContent KMap
    deriving (Eq, Ord, Show, Data, Typeable)
