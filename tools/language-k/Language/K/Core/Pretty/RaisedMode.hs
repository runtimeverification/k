-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Core.Pretty.RaisedMode
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- Pretty printer for K Core that tries to raise a K term to the original
-- syntax it encodes. In the future, this pretty printer will be configurable
-- with the precedence levels of the original syntax so as to reduce the
-- number of parentheses in the result.
-----------------------------------------------------------------------------

module Language.K.Core.Pretty.RaisedMode
    ( prettyPrint
    ) where

import Data.Char (isAlphaNum)
import Language.K.Core.Syntax

prettyPrint :: K -> String
prettyPrint = ppK

ppK :: K -> String
ppK (KApp (KLabel ps) as) = unwords $ zipSyntax ps (map ppK as)
ppK (KApp builtin _) = ppKBuiltin builtin

ppKBuiltin :: KLabel -> String
ppKBuiltin (KNat i)    = show i
ppKBuiltin (KInt i)    = show i
ppKBuiltin (KBool b)   = show b
ppKBuiltin (KString s) = show s
ppKBuiltin (KId s)     = s

-- | Combine a KLabel and a list of arguments to form the original syntax.
zipSyntax (Syntax s : xs) as = s : zipSyntax xs as
zipSyntax (Hole : xs) (a : as)
    -- Somewhat hackish way to reduce parentheses in output
    | all isAlphaNum a = a : zipSyntax xs as
    | otherwise = ("(" ++ a ++ ")") : zipSyntax xs as
zipSyntax _ _ = []
