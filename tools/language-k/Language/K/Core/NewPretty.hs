module Language.K.Core.NewPretty where

import Data.Map (fromList, toList)
import Language.K.Core.Syntax
import Text.PrettyPrint.ANSI.Leijen

printDoc doc = do
    putDoc doc
    putStrLn ""

ppK (KApp klabel ks) = ppKLabel klabel
ppK (Kra []) = char '.'

ppKLabel (KInt i) = integer i
ppKLabel (KId id) = text id
ppKLabel (KBool True) = text "true"
ppKLabel (KBool False) = text "false"
ppKLabel (KString s) = text (show s)

ppKBag (KBag []) = char '.'
ppKBag (KBag bs) = vsep $ map ppBagItem bs

ppBagItem (CellItem label content) =
    hang 2 (ppStartTag label <$> (ppCellContent content)) <$> ppEndTag label

ppKList (KList []) = char '.'
ppKList (KList ks) = vsep $ map ppK ks

ppKMap (KMap m) = vcat . map ppMapItem . toList $ m

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
