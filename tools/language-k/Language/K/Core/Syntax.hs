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

data K
    = KApp KLabel [K]
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
