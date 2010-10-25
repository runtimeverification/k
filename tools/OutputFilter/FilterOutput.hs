{-
  Filter the output of the k-framework tool
  Usage: runhaskell FilterOutput.hs <output_file> <config_file>

  See ParseConfig for how the config file should look
 -}

{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module FilterOutput where
  import ParseKOutput
  import ParseConfig
  import InfixOperators
  import ByteStringUtils
  import System.Environment
--  import Useful.String
  import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
  import Data.ByteString.Char8 (ByteString, unpack, pack, cons, uncons, append, singleton, snoc)
  import qualified Data.ByteString.Char8 as B
  import Control.Applicative ((<$>))
  import Control.Monad
  import Control.Monad.Identity
  import Control.Monad.State
  import Control.Monad.List
  import Data.List
  import Data.Maybe
  import qualified Data.Map as Map
  import Control.Monad.Reader
  import Text.Regex.Less
  import qualified Text.Regex.PCRE as PCRE
--  import Data.String.Utils
--  import Text.Regex.PCRE.Light.Char8

  type CellReader a  = Configuration -> CellName -> a
  type KOutReader a  = Configuration -> KOutput -> a
  type StyleReader a = CellReader ((CellConfigRhs -> Maybe Style) -> a)

  type KOutPrinter = KOutReader Doc
  type CellPrinter = CellReader ([KOutput] -> Doc)
  type Query = CellReader Bool


  -- Strip off surrounding whitespaces, remove empty strings, remove those blasted DOS carriage returns
  cleanupStrings :: [KOutput] -> [KOutput]
  cleanupStrings = remEmpty . map stripStrs
    where stripStrs (String n s) = String n (rstrip (deleteAll '\r' s))
          stripStrs x            = x
          remEmpty (String _ s : xs) | s == "" = remEmpty xs
          remEmpty (x:xs)                      = x : remEmpty xs
          remEmpty []                          = []


  handleCell :: KOutPrinter
  handleCell conf (Cell name contents) | shouldShow conf name    = ppCell conf name contents
                                       | shouldRecHide conf name = empty
                                       | otherwise               = ppHiddenCell conf name contents
  handleCell _ (String n s) = error $ "Internal error: handleCell called in cell: " ++ unpack n ++ "on string: " ++ unpack s

  ppCell :: CellPrinter
  ppCell conf name contents = linebreak <> (hang 1 $ ppBeginCell conf name
                                                  <> handleContents conf name contents
                                                 <+> ppEndCell conf name)

  ppHiddenCell :: CellPrinter
  ppHiddenCell conf name contents = hcat $ map (handleCell conf) onlyCells
    where onlyCells = filter isCell contents

  handleContents :: CellPrinter
  handleContents conf name cs = hcat $ (map (ppKOutput conf) . cleanupStrings)  cs

  handleString :: KOutPrinter
  handleString conf (String n s) = handleHilighting conf $ handleStyle conf n textStyle . text . unpack . pruneChars conf n . handleSubstitutions conf n . pruneLines conf n . handleInfix conf $ s
  {-
    Pretty Printing
   -}

  ppBeginCell :: CellReader Doc
  ppBeginCell conf n = handleStyle conf n cellStyle . text $ if shouldSpacelessCells conf then "<" ++ unpack n ++ ">"
                                                             else "< " ++ unpack n ++ " >"

  ppEndCell :: CellReader Doc
  ppEndCell conf n = handleStyle conf n cellStyle . text $  if shouldSpacelessCells conf then "</" ++ unpack n ++ ">"
                                                             else "</ " ++ unpack n ++ " >"

  ppKOutput :: Configuration -> KOutput -> Doc
  ppKOutput conf str@(String _ _) = handleString conf str
  ppKOutput conf cell@(Cell _ _)  = handleCell conf cell

  isCell (Cell _ _) = True
  isCell _          = False

  isString (String _ _ ) = True
  isString _             = False

  handleInfix :: Configuration -> ByteString -> ByteString
  handleInfix conf s | shouldInfixify conf = makeInfix s
                     | otherwise           = s

  handleStyle :: StyleReader (Doc -> Doc)
  handleStyle conf name f | hasStyle conf name f = stylize (fetchStyle conf name f)
                          | otherwise            = id

  handleHilighting :: Configuration -> Doc -> Doc
  handleHilighting conf doc | False              = undefined
                            | otherwise          = doc

  -- extend me to do local substitutions as well
  handleSubstitutions :: CellReader (ByteString -> ByteString)
  handleSubstitutions conf n s | hasSubs conf n = performSubs s $ fetchSubs conf
                               | otherwise = s

  performSubs :: ByteString -> [Substitution] -> ByteString
  performSubs s (Substitution re repl : subs) = performSubs (performReplacement re repl s) subs
  performSubs s [] = s

  performReplacement :: ByteString -> ByteString -> ByteString -> ByteString
  performReplacement old new s = pack $ mySubG (unpack old) (unpack new) (unpack s)


  -- Perform a substitution
  mySub :: String -> String -> String -> String
  mySub old new s = case s =~ old of
                      m@(_,x:xs) -> subs m new
                      _          -> s
  -- Performa all substitutions, pcre-less seems to have several bugs in it with their subg
  mySubG :: String -> String -> String -> String
  mySubG old new s = if s == mySub old new s then s
                     else mySubG old new (mySub old new s)

  stylize :: Style -> Doc -> Doc
  stylize (Style fore back isUnder isBold) = doUnder isUnder . doBold isBold . doFore fore . doBack back
    where doUnder Nothing            = id
          doUnder (Just Underline)   = underline
          doUnder (Just DeUnderline) = deunderline
          doBold Nothing       = id
          doBold (Just Bold)   = bold
          doBold (Just DeBold) = debold
          doFore Nothing  = id
          doFore (Just c) = colorize c Foreground
          doBack Nothing  = id
          doBack (Just c) = colorize c Background

  colorize :: Color -> ColorPlace -> (Doc -> Doc)
  colorize c Foreground = case c of
                            Black       -> black
                            Red         -> red
                            Green       -> green
                            Yellow      -> yellow
                            Blue        -> blue
                            Magenta     -> magenta
                            Cyan        -> cyan
                            White       -> white
                            Dullblack   -> dullblack
                            Dullred     -> dullred
                            Dullgreen   -> dullgreen
                            Dullyellow  -> dullyellow
                            Dullblue    -> dullblue
                            Dullmagenta -> dullmagenta
                            Dullcyan    -> dullcyan
                            Dullwhite   -> dullwhite
  colorize c Background = case c of
                            Black       -> onblack
                            Red         -> onred
                            Green       -> ongreen
                            Yellow      -> onyellow
                            Blue        -> onblue
                            Magenta     -> onmagenta
                            Cyan        -> oncyan
                            White       -> onwhite
                            Dullblack   -> ondullblack
                            Dullred     -> ondullred
                            Dullgreen   -> ondullgreen
                            Dullyellow  -> ondullyellow
                            Dullblue    -> ondullblue
                            Dullmagenta -> ondullmagenta
                            Dullcyan    -> ondullcyan
                            Dullwhite   -> ondullwhite

  -- Prune off lines after the user-specified break
  -- doPrunes :: Configuration -> CellName -> ByteString -> ByteString
  -- doPrunes conf cn = pruneLines conf cn . pruneChars conf cn

  pruneLines :: Configuration -> CellName -> ByteString -> ByteString
  pruneLines conf cn s | shouldPrune conf cn = pruneL conf cn s
                       | otherwise           = s

  pruneChars :: Configuration -> CellName -> ByteString -> ByteString
  pruneChars conf cn s | shouldPruneChars conf cn = pruneC conf cn s
                       | otherwise                = s

  pruneL :: Configuration -> CellName -> ByteString -> ByteString
  pruneL conf cn s = B.unlines takenLines `append` more
    where takenLines = take toTake intermediate
          intermediate = B.lines s
          toTake = fetchPruneNumber conf cn
          more = if toTake >= length intermediate then ""
                 else pack $ indentation takenLines ++ " [..." ++ show (length intermediate - length takenLines)
                          ++ " more...]"
          indentation (s:s2:ss) = replicate (B.length (B.takeWhile (== ' ') s2)) ' '
          indentation _         = replicate 8 ' ' -- Otherwise just use 8 space indentation

  pruneC :: Configuration -> CellName -> ByteString -> ByteString
  pruneC conf cn = rstrip . B.unlines . map truncAndAdd . B.lines
    where toKeep = fetchPruneCharNumber conf cn
          truncAndAdd s = if B.length s > toKeep then B.take toKeep s `append` lineEndStr
                          else s
          lineEndStr | hasOption conf lineEnd = fetchLineEnd conf
                     | otherwise              = ""

  -- Lookup the config for the cell
  lookupCell :: CellReader (Maybe CellConfigRhs)
  lookupCell = flip Map.lookup

  lookupOptions = Map.lookup "options"

  queryOptions :: Configuration -> (CellConfigRhs -> Maybe Bool) -> Bool
  queryOptions conf f = case f <$> lookupOptions conf of
                          Just (Just True) -> True
                          _                -> False

  hasOption :: Configuration -> (CellConfigRhs -> Maybe a) -> Bool
  hasOption conf f = case f <$> lookupOptions conf of
                       Just (Just _) -> True
                       _             -> False

  shouldSpacelessCells :: Configuration -> Bool
  shouldSpacelessCells conf = queryOptions conf spacelessCells

  shouldInfixify :: Configuration -> Bool
  shouldInfixify conf = queryOptions conf infixify

  -- Should a cell be shown?
  shouldShow :: Query
  shouldShow cn conf = case lookupCell cn conf of
                         Just Hide          -> False
                         Just RecursiveHide -> False
                         Nothing            -> False
                         _                  -> True

   -- Should a cell be recursively hidden?
  shouldRecHide :: Query
  shouldRecHide conf cn = case lookupCell conf cn of
                            Just RecursiveHide -> True
                            _                  -> False

  -- Should a cell be pruned?
  shouldPrune :: Query
  shouldPrune conf cn = case lookupCell conf cn of
                          Just (Configs (Just _) _ _ _ _ ) -> True
                          _                                -> False

  shouldPruneChars :: Query
  shouldPruneChars conf cn = case lookupCell conf cn of
                               Just (Configs _ (Just _) _ _ _ ) -> True
                               _                                -> False


  hasSubs :: Query
  hasSubs conf cn = if hasGlobalSubs conf then True
                    else case lookupCell conf cn of
                           Just (Configs _ _ _ _ (Just _)) -> True
                           _                               -> False
    where hasGlobalSubs conf = case lookupCell conf "options" of
                                 Nothing                         -> False
                                 Just (Options Nothing _ _ _ _ ) -> False
                                 _                               -> True



  hasStyle :: StyleReader Bool
  hasStyle conf cn f = case lookupCell conf cn of
                           Just c@(Configs _ _ _ _ _) -> isJust (f c)
                           _                          -> False

  fetchStyle :: StyleReader Style
  fetchStyle conf cn f = case lookupCell conf cn >>= f of
                         Just s -> s
                         _      -> error "Internal Error: hasStyle approved a cell incorrectly"

  -- Fetch the number of lines to keep from the configuration
  fetchPruneNumber :: CellReader Int
  fetchPruneNumber conf cn = case lookupCell conf cn >>= keepLines of
                             Just n -> n
                             _      -> error "Internal Error: shouldPrune approved a prune candidate incorrectly"

  fetchPruneCharNumber :: CellReader Int
  fetchPruneCharNumber conf cn = case lookupCell conf cn >>= keepChars of
                                   Just n -> n
                                   _      -> error "Internal Error: shouldPruneChar approved a prune candidate incorrectly"


  -- Extend me to do local subs
  fetchSubs :: Configuration -> [Substitution]
  fetchSubs = (flip fetchOption) globalSubstitutions

  fetchLineEnd :: Configuration -> ByteString
  fetchLineEnd = (flip fetchOption) lineEnd

  fetchOption :: Configuration -> (CellConfigRhs -> Maybe a) -> a
  fetchOption conf f = case f <$> lookupOptions conf of
                         Just (Just a) -> a
                         Just Nothing  -> error "Internal Error: option not found"
                         Nothing       -> error "Internal Error: option cell not specified"

  -- Whether a maybe is something

  -- Convert to string
  -- stringifyDoc :: Doc -> String
  -- stringifyDoc doc = tail $ (displayS $ renderPretty 1.0 80 doc) ""


  -- Todo: implement real argument parsing, and real error handling
  main :: IO ()
  main = do args <- getArgs
            (fname, configFile) <- case args of
                       (x:y:xs) -> return (x,y)
                       _   -> error usage
            parsedOut <- parseKOutFile fname
            config <- getConfig configFile
--            print config
            putDoc . cat . map (ppKOutput config) $ parsedOut
            putStrLn ""

  usage = "\nUsage:\n" ++ "  If you have built the tool using 'make', then run:\n"
                       ++ "    filterOutput <output-file> <yaml-config-file>\n"
                       ++ "  To run the tool without building it, run:\n"
                       ++ "    runhaskell FilterOutput.hs <output-file> <yaml-config-file>\n"
