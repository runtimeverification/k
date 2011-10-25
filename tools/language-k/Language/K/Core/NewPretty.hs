module Language.K.Core.NewPretty where

import Data.Char (isAlphaNum)
import Data.List (intersperse)
import Data.Map (fromList, toList)
import qualified Data.Map as Map
import Language.K.Core.Syntax
import Text.PrettyPrint.ANSI.Leijen

printDoc doc = do
    putDoc doc
    putStrLn ""

ppK (Kra []) = char '.'
ppK (Kra ks) = hsep $ intersperse (yellow $ text "~>") (map ppK ks)
ppK (KApp klabel []) = ppKLabel klabel
ppK (KApp (KLabel ss) ks) = hsep $ zipSyntax ss (map ppK ks)
ppK (KApp klabel ks) = ppKLabel klabel <> parens (hsep $ punctuate comma (map ppK ks))

-- | Combine a KLabel and a list of arguments to form the original syntax.
zipSyntax (Syntax s : xs) as = bold (text s) : zipSyntax xs as
zipSyntax (Hole : xs) (a : as)
    -- Somewhat hackish way to reduce parentheses in output
    | all isAlphaNum (show a) = a : zipSyntax xs as
    | otherwise = parens a : zipSyntax xs as
zipSyntax _ _ = []

ppKLabel (KInt i) = integer i
ppKLabel (KId id) = text id
ppKLabel (KBool True) = text "true"
ppKLabel (KBool False) = text "false"
ppKLabel (KString s) = text (show s)
ppKLabel (Freezer s) = text "freezer" <> parens (text s)
ppKLabel (FreezeVar s) = blue $ text s
--ppKLabel (FreezeVar s) = text "freezerVar" <> parens (text s)

ppKBag (KBag []) = char '.'
ppKBag (KBag bs) = vsep $ map ppBagItem bs

ppBagItem (BagItem k) = text "BagItem" <> parens (ppK k)
ppBagItem (CellItem label content) =
    hang 2 (ppStartTag label <$> (ppCellContent content)) <$> ppEndTag label

ppKList (KList []) = char '.'
ppKList (KList ls) = vsep $ map ppListItem ls

ppListItem (ListItem k) = text "ListItem" <> parens (ppK k)
ppListItem (Buffer k) = ppK k
ppListItem (IStream 0) = angles $ text "stdin"
ppListItem (IStream i) = angles $ text "istream: " <> integer i
ppListItem (OStream 1) = angles $ text "stdout"
ppListItem (OStream 2) = angles $ text "stderr"
ppListItem (OStream i) = angles $ text "ostream: " <> integer i

ppKMap (KMap m)
    | m == Map.empty = char '.'
    | otherwise = vcat . map ppMapItem . toList $ m

ppMapItem (k1, k2) = ppK k1 <+> magenta (text "|->") <+> ppK k2

ppCellContent (KContent k) = ppK k
ppCellContent (BagContent bag) = ppKBag bag
ppCellContent (ListContent list) = ppKList list
ppCellContent (MapContent map) = ppKMap map

ppStartTag label = green $ char '<' <> text label <> char '>'
ppEndTag label = green $ text "</" <> text label <> char '>'


{- Some test cases: -}

simpleTest = KBag [CellItem {cellItemLabel = "a", cellItemContent = KContent (KApp (KInt 42) [])}]

sumPgmTest = KBag [CellItem {cellItemLabel = "T", cellItemContent = BagContent (KBag [CellItem {cellItemLabel = "k", cellItemContent = KContent (Kra [])},CellItem {cellItemLabel = "state", cellItemContent = MapContent (KMap (fromList [(KApp (KId "n") [],KApp (KInt 0) []),(KApp (KId "s") [],KApp (KInt 55) [])]))}])}]

countPrimesPgmTest = KBag [CellItem {cellItemLabel = "T", cellItemContent = BagContent (KBag [CellItem {cellItemLabel = "k", cellItemContent = KContent (Kra [])},CellItem {cellItemLabel = "state", cellItemContent = MapContent (KMap (fromList [(KApp (KId "i") [],KApp (KInt 2) []),(KApp (KId "n") [],KApp (KInt 21) []),(KApp (KId "q") [],KApp (KInt 0) []),(KApp (KId "r") [],KApp (KInt 1) []),(KApp (KId "s") [],KApp (KInt 8) []),(KApp (KId "t") [],KApp (KInt 0) []),(KApp (KId "upTo") [],KApp (KInt 20) []),(KApp (KId "x") [],KApp (KInt 0) []),(KApp (KId "y") [],KApp (KInt 40) []),(KApp (KId "z") [],KApp (KInt 20) [])]))}])}]
