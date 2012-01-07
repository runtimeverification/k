-----------------------------------------------------------------------------
-- |
-- Module      :  Language.K.Core.Pretty
-- Copyright   :  (c) David Lazar, 2011
-- License     :  MIT
--
-- Maintainer  :  lazar6@illinois.edu
-- Stability   :  experimental
-- Portability :  unknown
--
-- Convert (pretty print) a K Core AST into an actual K term that is usable
-- in the K framework.
-----------------------------------------------------------------------------

-- TODO: The pretty printer is slow to execute; it desperately needs to be
-- optimized.

module Language.K.Core.Pretty
    ( prettyPrint
    ) where

import Data.List (intercalate)
import Language.K.Core.Syntax

prettyPrint :: K -> String
prettyPrint = ppK

ppK :: K -> String
ppK (KApp klabel argv) = ppKLabel klabel ++ "(" ++ ppKlist argv ++ ")"

{-
Old way of pretty-printing builtins:

ppKLabel :: KLabel -> String
ppKLabel (KNat i)      = "#Nat " ++ show i
ppKLabel (KInt i)      = "#Int " ++ show i
ppKLabel (KBool True)  = "#Bool true"
ppKLabel (KBool False) = "#Bool false"
ppKLabel (KString s)   = "#String " ++ show s
ppKLabel (KId s)       = "#Id " ++ s
-}
ppKLabel :: KLabel -> String
ppKLabel (KNat i)      = "# " ++ show i
ppKLabel (KInt i)      = "# " ++ show i
ppKLabel (KBool True)  = "# true"
ppKLabel (KBool False) = "# false"
ppKLabel (KString s)   = "# " ++ show s
ppKLabel (KId s)       = "# " ++ s
ppKLabel (KLabel ps)   = '\'' : concatMap ppPart ps
    where ppPart (Syntax s) = maudeEscape s
          ppPart Hole = "_"

ppKlist [] = ".List{K}"
ppKlist ks = intercalate ",," (map ppK ks)

-- | Turn a string into a Maude identifier by escaping the necessary
-- characters.
maudeEscape :: String -> String
maudeEscape = concatMap escape
    where escape c | c `elem` "{}()[]," = ['`', c]
                   | otherwise = [c]
