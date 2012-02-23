{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Language.K.Core.Prettier where

import Data.List (intersperse, stripPrefix)
import qualified Data.Monoid as M
import Language.K.Core.Syntax
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Control.Monad.Reader

prettierPrint :: (Pretty a) => PrettyConfig -> a -> IO ()
prettierPrint conf p = do
    PP.putDoc $ runReader (runKPP $ pretty p) conf
    putStrLn ""

-- | Configuration for the pretty-printer
data PrettyConfig = PrettyConfig
    { useColor :: Bool
    , noParens :: Bool
    } deriving (Eq, Ord, Show)

-- | Pretty-printer monad
newtype KPP a = KPP
    { runKPP :: Reader PrettyConfig a
    } deriving (Functor, Monad, MonadReader PrettyConfig)

instance M.Monoid (KPP PP.Doc) where
    mempty = empty
    mappend = liftM2 M.mappend


-- monadic variants of the pretty-printer combinators:
infixr 6 <>
(<>) :: (M.Monoid a) => a -> a -> a
(<>) = M.mappend

(<+>) = liftM2 (PP.<+>)
(<$$>) = liftM2 (PP.<$$>)

char = return . PP.char
text = return . PP.text
empty = return PP.empty
comma = return PP.comma
integer i = return $ PP.integer i
parens = liftM PP.parens 
hang i = liftM (PP.hang i)
nest i = liftM (PP.nest i)
align = liftM PP.align
hsep = liftM PP.hsep
vsep = liftM PP.vsep
hcat = liftM PP.hcat
vcat = liftM PP.vcat
punctuate = liftM2 PP.punctuate

-- | Print color depending on the configuration.
color :: (PP.Doc -> PP.Doc) -> KPP PP.Doc -> KPP PP.Doc
color c doc = do
    uc <- asks useColor
    if uc then fmap c doc else doc

bold = color PP.bold
red = color PP.red
blue = color PP.blue
green = color PP.green
magenta = color PP.magenta

class Pretty a where
    pretty :: a -> KPP PP.Doc

instance Pretty K where
    pretty (Kra []) = char '.'
    pretty (Kra ks) = hsep . sequence $ intersperse karr (map pretty ks)
        where karr = bold . blue $ (text "~>")
    -- ugly special-case for Lists to avoid pretty-printing .List{"X"}
    pretty (KApp klabel [k, KApp emptyList []])
        | Just cons1 <- getListCons klabel
        , Just cons2 <- getListCons emptyList
        , cons1 == cons2
        = pretty k
    pretty (KApp (Freezer k) ks) = pretty $ plugFreezer k ks
    pretty (KApp klabel []) = pretty klabel
    pretty (KApp (KLabel ss) ks) = hsep $ zipSyntax ss ks
    pretty (KApp klabel ks) = pretty klabel <> parens (hsep $ punctuate comma (mapM pretty ks))
    --pretty FreezerHole = text "□"
    pretty FreezerHole = text "HOLE"
    -- shouldn't happen:
    pretty (FreezerVar s) = red $ text s

getListCons :: KLabel -> Maybe String
getListCons (KLabel [Syntax l]) = do
    x <- stripPrefix ".List{" l
    case reads x of
        [(str, "}")] -> return str
        _ -> Nothing
getListCons (KLabel [Hole, Syntax l, Hole]) = Just l
getListCons _ = Nothing

plugFreezer :: K -> [K] -> K
plugFreezer k ks = mapK (plug ks) k
    where plug :: [K] -> K -> K
          -- TODO: this equation is probably no longer needed:
          plug _ (FreezerVar "HOLE") = FreezerHole
          plug ks (FreezerVar var) = lookupK var ks
          plug _ k = k

          lookupK :: String -> [K] -> K
          -- TODO: unsafe
          lookupK var ks =
            let rs = [ k | (KApp (FreezerMap var') [k]) <- ks, var == var' ]
            in case rs of
                [] -> error $ "unable to find mapping for variable " ++ var
                (r:_) -> r

          mapK :: (K -> K) -> K -> K
          mapK f (KApp label ks) = KApp label (map f ks)
          mapK f (Kra ks) = Kra (map f ks)
          mapK f k = k

-- | Combine a KLabel and a list of arguments to form the original syntax.
zipSyntax :: [KLabelPart] -> [K] -> KPP [PP.Doc]
zipSyntax (Syntax s : xs) ks = liftM2 (:) (bold (text s)) (zipSyntax xs ks)
-- TODO: need original precedences, etc to get the parentheses right.
zipSyntax (Hole : xs) (k : ks) = do
    np <- asks noParens
    let f = if np || not (needsParens k) then id else parens
    liftM2 (:) (f $ pretty k) (zipSyntax xs ks)
zipSyntax _ _ = return []

needsParens (Kra []) = False
needsParens (KApp kl []) = not (isBuiltin kl)
-- ugly special-case for Lists again
needsParens (KApp klabel [k, KApp emptyList []])
    | Just cons1 <- getListCons klabel
    , Just cons2 <- getListCons emptyList
    , cons1 == cons2
    = False
needsParens (KApp (KLabel kls) ks) = not (isSyntax (head kls) && isSyntax (last kls))
    where isSyntax (Syntax _) = True
          isSyntax _ = False
needsParens FreezerHole = False
needsParens _ = True

isBuiltin (KInt _) = True
isBuiltin (KString _) = True
isBuiltin (KBool _) = True
isBuiltin (KId _) = True
isBuiltin _ = False

instance Pretty KLabel where
    pretty (KSym i) = text "sym(" <> integer i <> text ")" -- TODO
    pretty (KInt i) = integer i
    pretty (KId id) = text id
    pretty (KBool True) = text "true"
    pretty (KBool False) = text "false"
    pretty (KString s) = text (show s)
    pretty (Freezer k) = text "freezer" <> parens (pretty k)
    -- don't print .List{"X"}:
    pretty kl | Just _ <- getListCons kl = empty
    pretty (KLabel ss) = hcat $ mapM ppSyntax ss
        where ppSyntax (Syntax s) = text s
              ppSyntax Hole = char '_'
    pretty (WMap kmap) = pretty kmap
    pretty (WBag kbag) = pretty kbag
    pretty (WKList str) = empty  -- TODO: good enough for now
    pretty kl = error $ "No pretty-printer available for: " ++ show kl

instance Pretty KBag where
    pretty (KBag []) = char '.'
    pretty (KBag bs) = vsep $ mapM pretty bs

instance Pretty BagItem where
    pretty (BagItem k) = text "BagItem" <> parens (pretty k)
    pretty (CellItem label content) =
        align (nest 2 (ppStartTag label <$$> pretty content) <$$> ppEndTag label)

ppStartTag label = green $ char '<' <> text label <> char '>'
ppEndTag label = green $ text "</" <> text label <> char '>'

instance Pretty KSet where
    pretty (KSet []) = char '.'
    pretty (KSet ks) = vsep $ mapM pretty ks

instance Pretty KList where
    pretty (KList []) = char '.'
    pretty (KList ls) = vsep $ sequence [ pretty l | l <- ls, not (isStream l) ]
        where isStream (IStream _) = True
              isStream (OStream _) = True
              isStream _ = False

instance Pretty ListItem where
    pretty (ListItem k) = text "ListItem" <> parens (pretty k)
    pretty (Buffer k) = pretty k
    pretty (IStream _) = empty
    pretty (OStream _) = empty
{-
ppListItem (IStream 0) = angles $ text "stdin"
ppListItem (IStream i) = angles $ text "istream: " <> integer i
ppListItem (OStream 1) = angles $ text "stdout"
ppListItem (OStream 2) = angles $ text "stderr"
ppListItem (OStream i) = angles $ text "ostream: " <> integer i
-}

instance Pretty KMap where
    pretty (KMap m)
        | null m = char '.'
        | otherwise = vcat $ mapM pretty m

-- MapItem
instance Pretty (K, K) where
    pretty (k1, k2) = pretty k1 <+> magenta (text "|->") <+> pretty k2

instance Pretty CellContent where
    pretty (KContent k) = pretty k
    pretty (BagContent bag) = pretty bag
    pretty (ListContent list) = pretty list
    pretty (MapContent map) = pretty map
    pretty (SetContent set) = pretty set
    pretty (NoParse str) = red (char '(') <> text str <> red (char ')')



{- Some test cases: -}

simpleTest = KBag [CellItem {cellItemLabel = "a", cellItemContent = KContent (KApp (KInt 42) [])}]

sumPgmTest = KBag [CellItem {cellItemLabel = "T", cellItemContent = BagContent (KBag [CellItem {cellItemLabel = "k", cellItemContent = KContent (Kra [])},CellItem {cellItemLabel = "state", cellItemContent = MapContent (KMap [(KApp (KId "n") [],KApp (KInt 0) []),(KApp (KId "s") [],KApp (KInt 55) [])])}])}]

countPrimesPgmTest = KBag [CellItem {cellItemLabel = "T", cellItemContent = BagContent (KBag [CellItem {cellItemLabel = "k", cellItemContent = KContent (Kra [])},CellItem {cellItemLabel = "state", cellItemContent = MapContent (KMap [(KApp (KId "i") [],KApp (KInt 2) []),(KApp (KId "n") [],KApp (KInt 21) []),(KApp (KId "q") [],KApp (KInt 0) []),(KApp (KId "r") [],KApp (KInt 1) []),(KApp (KId "s") [],KApp (KInt 8) []),(KApp (KId "t") [],KApp (KInt 0) []),(KApp (KId "upTo") [],KApp (KInt 20) []),(KApp (KId "x") [],KApp (KInt 0) []),(KApp (KId "y") [],KApp (KInt 40) []),(KApp (KId "z") [],KApp (KInt 20) [])])}])}]
