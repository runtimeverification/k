{-# LANGUAGE ViewPatterns, GeneralizedNewtypeDeriving, PatternGuards #-}
module Main(main) where
import ATerm.ReadWrite(readATerm)
import ATerm.AbstractSyntax(ATermTable,getTopIndex,ShATerm(..),getShATerm)
import Data.List(nub,intercalate,isSuffixOf)
import Data.Function (on)
import qualified Data.Map as Map
import Data.Map(Map)
import System.Environment(getArgs)
import System.Exit(exitFailure)
import System.IO(hPutStr,stderr)

{- Decode an imploded sdf parse into Kast, using a table of constructor information -}

maudeSpecial :: [Char]
maudeSpecial = "`,{}[]()"

maudeEscape :: String -> String
maudeEscape (c:cs)
  | c `elem` maudeSpecial = '`':c:maudeEscape cs
  | otherwise = c:maudeEscape cs
maudeEscape [] = []

kastSpecial :: [Char]
kastSpecial = "`()"

kastEscape :: String -> String
kastEscape s = escape s
  where escape (c:cs)
          | c `elem` kastSpecial = '`':c:escape cs
          | otherwise = c:escape cs
        escape [] = []

unescapeSortName ('D':'d':s) = 'D':s
unescapeSortName ('D':'z':s) = '#':s
unescapeSortName ('D':'l':s) = '{':s
unescapeSortName ('D':'r':s) = '}':s
unescapeSortName (c:s) = c:unescapeSortName s
unescapeSortName [] = []

{- Simplified representation of the ATerms found in parse results -}
data ATm = AAp String [Int] | ALst [Int] deriving Show

shToATm :: ShATerm -> ATm
shToATm (ShAAppl s cs []) = AAp s cs
shToATm (ShAList cs []) = ALst cs
shToATm s = error $ "unexpected ATerm node in parse result "++show s

{- Table of constructor information. Constructors are brackets,
   productions with a klabel, or user lists with a klabel
   to use as "cons" and a separator for forming the .List. 
   Each production may also be tagged as prefer. 
   See also MaudeFilter.java -}
splitTab :: String -> (String,String)
splitTab s = let (first,rest) = break(=='\t') s in (first, drop 1 rest)

data ConsKind = Plain String | Bracket | UserList String String -- label, separator
  deriving Show
data ConsInfo = ConsInfo Bool ConsKind -- prefer
  deriving Show

parseConsTbl :: String -> Map String ConsInfo
parseConsTbl t = Map.fromList
  [(a,ConsInfo (p=='*') (lblInfo b)) | (a,p:b) <- map splitTab (filter ((/="#").take 1) (lines t))]
 where lblInfo "B" = Bracket                 
       lblInfo ('P':klabel) = Plain (unescape $ klabel)
       lblInfo ('L':lstinfo) =
         let (label,sep) = splitTab lstinfo
         in UserList (unescape $ label) (unescape sep)
       lblInfo k = error $ "Bad production info string "++show k

unescape :: String -> String
unescape str = read ('"':str++['"'])

escape :: String -> String
escape str = show str

loadConsTable :: FilePath -> IO (Map String ConsInfo)
loadConsTable tblFile = fmap parseConsTbl (readFile tblFile)

{- Representation of a KAst term.
   The string argument will be printed directly,
   and may be an entire constant -}
data KAst = KApp KLabel [KAst]
  deriving Show

data KLabel = KLabel String | Token String String -- content, sort
  deriving Show

mkConst :: String -> String -> KAst
mkConst val sort = KApp (Token val sort) []

-- Print a KAst term as kast does.
printMetaMetaMeta :: KAst -> String
printMetaMetaMeta (KApp label children) =
    "_`(_`)("++printLabel label++", "++args++") "
  where
    printLabel (Token n "#Int") = "#_("++n++")"
    printLabel (Token n "#Float") = "#_("++n++")"
    printLabel (Token b "#Bool") = "#_("++b++")"
    printLabel (Token s "#String") = "#_("++s++")"
    printLabel (Token s "KLabel") = "KLabel2KLabel_("++s++")"
    printLabel (Token val sort) = "#token("++show sort++", "++show val++")"
    printLabel (KLabel s) = maudeEscape s
    args = case map printMetaMetaMeta children of
      [] -> ".KList"
      [i] -> i
      cs -> "_`,`,_("++intercalate "," cs++")"

-- print according to new syntax
printKast :: KAst -> String
printKast (KApp label children) =
    printLabel label++"("++args++")"
  where
    printLabel (Token val sort) = "#token("++escape val++","++escape sort++")"
    printLabel (KLabel s) = kastEscape s
    args = case map printKast children of
      [] -> ".KList"
      cs -> intercalate "," cs

{- Decode a parse DAG into a parse result -}
gatherAmb :: ATermTable -> [Int] -> [Int]
gatherAmb tbl cs = nub . concatMap readAmb . nub $ cs
  where readAmb k = case getShATerm k tbl of
          ShAAppl "amb" ks [] -> gatherAmb tbl ks
          _ -> [k]

decode :: ATermTable -> Map String ConsInfo -> Int -> KAst
decode tbl consTable n =
  case node' n of
    AAp "amb" children ->
      let children' = gatherAmb tbl children
          isPreferred k = case node' k of (AAp c _) | Just (ConsInfo True _) <- Map.lookup c consTable -> True
                                          _ -> False
      in case if any isPreferred children' then filter isPreferred children' else children' of
        [c] -> decode' c
        _ -> error $ "unresolved ambiguity at node "++show n
    AAp "DzBool1Const" [node' -> AAp val []] ->
      case val of
        "\"true\"" -> mkConst "true" "#Bool"
        "\"false\"" -> mkConst "false" "#Bool"
        _ -> error $ "Unknown boolean value at node "++show n++" in parse:"++show val
    AAp "DzBool1Cons" _ ->
        error $ "Unknown boolean node with malformed children at node "++show n
    AAp "DzString1Const" cs ->
     case cs of
       [str' -> val] -> mkConst val "#String"
       _ -> error $ "malformed DzString1Const at node "++show n
    AAp "DzInt1Const" [str' -> val] ->
      mkConst val "#Int"
    AAp "DzFloat1Const" [str' -> val] ->
      mkConst val "#Float"
    AAp "KLabel1Const" [str' -> label] ->
        mkConst label "KLabel"
    AAp cons [str' -> tok]
      | "1Const" `isSuffixOf` cons ->
        let sort = unescapeSortName $ take (length cons - length "1Const") cons in
        mkConst tok sort
    AAp cons _
      | "1Const" `isSuffixOf` cons ->
        error $ "Don't know how to handle token production "++cons++" at node "++show n
    AAp cons [node' -> ALst children]
      | Just (UserList klabel sep) <- consInfo cons ->
          foldr (\i rest -> KApp (KLabel klabel) [i,rest])
                (KApp (KLabel ("'.List{"++show sep++"}")) [])
            (map decode' children)
    AAp cons [child]
       | Just Bracket <- consInfo cons -> decode' child
    AAp cons children ->
       case consInfo cons of
         Just (Plain klabel) ->
           KApp (KLabel klabel) (map decode' children)
         Just Bracket -> error $ "Malformed bracket at node "++show n
         Just (UserList _ _) -> error $ "Malformed user list at node "++show n
         Nothing ->
           error $ "Unknown cons label "++cons
    ALst _ ->
      error $ "Unexpected list at node "++show n
  where
    decode' = decode tbl consTable
    node t = getShATerm t tbl
    node' t = shToATm (node t)
    str' :: Int -> String
    str' k = case node' k of AAp s [] -> read s
                             t -> error $ "expected string at node "++show k++", found "++show t
    consInfo cons = case Map.lookup cons consTable of Just (ConsInfo _ k) -> Just k; Nothing -> Nothing

{- Decode the parse DAG received on standard input according to
   the constructor info table specified as an argument.
   Saves the parse DAG to "err.tbl" on errors -}
main :: IO ()
main = do
  args <- getArgs
  let (mode, tblFile) = case args of
        [tblFile] -> (printMetaMetaMeta, tblFile)
        ["--new-kast",tblFile] -> (printKast, tblFile)
  consTable <- loadConsTable tblFile
  tbl <- fmap readATerm getContents
  let top = getTopIndex tbl
  case getShATerm top tbl of
    ShAAppl "summary" _ _ -> do
       hPutStr stderr $ decodeSummary tbl top
       exitFailure
    _ -> putStrLn $ mode (decode tbl consTable top)

decodeSummary tbl k =
  case getShATerm k tbl of
    ShAAppl "summary" [_,_,node -> ShAList errs []] [] -> unlines (map (decodeError tbl) errs)
 where
  node = flip getShATerm tbl

decodeError tbl k =
    case node k of
      ShAAppl "error"
        [node -> ShAAppl (read -> msg) [] [],
         node -> ShAList
                   [node -> ShAAppl "localized"
                              [_,
                               node -> ShAAppl "area-in-file"
                                          [node -> ShAAppl (read -> file) [] []
                                          ,loc] []] []] []] []
        -> "Critical: "++msg++"\nFile: "++file++"\nLocation: "++show (decodeLoc tbl loc)
  where
    node k = getShATerm k tbl

decodeLoc tbl k =
  case node k of
    ShAAppl "area"
      [node -> ShAInt r [],
       node -> ShAInt c [],
       node -> ShAInt r' [],
       node -> ShAInt c' [],
       _,
       _] [] -> (r,c,r',c')
 where
  node k = getShATerm k tbl 
