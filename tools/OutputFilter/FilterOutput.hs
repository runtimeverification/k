{-
  Filter the output of the k-framework tool
  Usage: runhaskell FilterOutput.hs <output_file> <config_file>

  See ParseConfig for how the config file should look
 -}

{-# OPTIONS -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}

module FilterOutput where
  import ParseKOutput
  import ParseConfig
  import System.Environment
  import Useful.String
  import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
  import Control.Applicative ((<$>))
  import Control.Monad
  import Control.Monad.Identity
  import Control.Monad.State
  import Control.Monad.List
  import Data.List
  import Data.Maybe
  import qualified Data.Map as Map
  import Control.Monad.Reader
  import Data.String.Utils
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
    where stripStrs (String n s) = String n (stripr (deleteAll '\r' s))
          stripStrs x            = x
          remEmpty (String _ "" : xs) = remEmpty xs
          remEmpty (x:xs)             = x : remEmpty xs
          remEmpty []                 = []

  -- Delete all occurrences
  deleteAll :: Eq a => a -> [a] -> [a]
  deleteAll x = filter ((/=) x)

  handleCell :: KOutPrinter
  handleCell conf (Cell name contents) | shouldShow conf name    = ppCell conf name contents
                                       | shouldRecHide conf name = empty
                                       | otherwise               = ppHiddenCell conf name contents
  handleCell _ (String n s) = error $ "Internal error: handleCell called in cell: " ++ n ++ "on string: " ++ s

  ppCell :: CellPrinter
  ppCell conf name contents = linebreak <> (hang 1 $ ppBeginCell conf name
                                                  <> handleContents conf name contents
                                                 <+> ppEndCell conf name)

  ppHiddenCell :: CellPrinter
  ppHiddenCell conf name contents = hcat $ map (handleCell conf) onlyCells
    where onlyCells = filter isCell contents

  handleContents :: CellPrinter
  handleContents conf name cs = hcat $ (map (ppKOutput conf) . doPrune conf name . cleanupStrings)  cs

  handleString :: KOutPrinter
  handleString conf (String n s) = handleStyle conf n textStyle . text . handleSubstitutions conf n $ s
  {-
    Pretty Printing
   -}

  ppBeginCell :: CellReader Doc
  ppBeginCell conf n = handleStyle conf n cellStyle . text $ "< " ++ n ++ " >"

  ppEndCell :: CellReader Doc
  ppEndCell conf n = handleStyle conf n cellStyle . text $ "</ " ++ n ++ " >"

  ppKOutput :: Configuration -> KOutput -> Doc
  ppKOutput conf str@(String _ _) = handleString conf str
  ppKOutput conf cell@(Cell _ _) = handleCell conf cell

  isCell (Cell _ _) = True
  isCell _          = False

  isString (String _ _ ) = True
  isString _             = False


  handleStyle :: StyleReader (Doc -> Doc)
  handleStyle conf name f | hasStyle conf name f = stylize (fetchStyle conf name f)
                          | otherwise            = id

  -- extend me to do local substitutions as well
  handleSubstitutions :: CellReader (String -> String)
  handleSubstitutions conf n s | hasSubs conf n = performSubs s $ fetchSubs conf n
                               | otherwise = s

  performSubs :: String -> [Substitution] -> String
  performSubs s (Substitution re repl : subs) = performSubs (performReplacement re repl s) subs
  performSubs s [] = s

  -- performReplacement re repl s = case match re s [] of
  --                                  Just ss -> replace (head ss) repl s
  --                                  Nothing -> s
  performReplacement = replace


  -- getMatch :: Regex -> String -> Maybe String
  -- getMatch re s = head <$> match re s []

  stylize :: Style -> Doc -> Doc
  stylize (Style fore back isUnder isBold) d = doUnder isUnder . doBold isBold . doFore fore . doBack back $ d
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
  doPrune :: Configuration -> CellName -> [KOutput] -> [KOutput]
  doPrune conf cn = pruneChars conf cn . pruneLines conf cn

  pruneLines :: Configuration -> CellName -> [KOutput] -> [KOutput]
  pruneLines conf cn ks | shouldPrune conf cn = map (pruneL conf cn) (filter isString ks)
                        | otherwise           = ks

  pruneChars :: Configuration -> CellName -> [KOutput] -> [KOutput]
  pruneChars conf cn ks | shouldPruneChars conf cn = map (pruneC conf cn) (filter isString ks)
                        | otherwise                = ks


  pruneL conf cn (String n s) = String n $ (stripr . unlines . take toKeep) intermediate ++ more
    where toKeep = fetchPruneNumber conf cn
          intermediate = lines s
          more = " [..." ++ show (length intermediate - 1) ++ " more...]"

  pruneC conf cn (String n s) = String n $ (stripr . unlines . map (take toKeep)) intermediate
    where toKeep = fetchPruneCharNumber conf cn
          intermediate = lines s

  -- Lookup the config for the cell
  lookupCell :: CellReader (Maybe CellConfigRhs)
  lookupCell = flip Map.lookup


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
    where hasGlobalSubs conf = case lookupCell conf "global-substitutions" of
                                 Nothing -> False
                                 _       -> True



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
  fetchSubs :: CellReader [Substitution]
  fetchSubs conf cn = case lookupCell conf "global-substitutions" of
                        Just (Configs _ _ _ _ (Just subs)) -> subs
                        Nothing -> error "Internal Error: hasSubs approved a match incorrectly"
                        _       -> error "Unable to find the global-substitutions cell"

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

  usage = "\nUsage:\n" ++ "  If you have built the tool using 'make', then run:\n"
                     ++ "    filterOutput <output-file> <yaml-config-file>\n"
                     ++ "  To run the tool without building it, run:\n"
                     ++ "    runhaskell FilterOutput.hs <output-file> <yaml-config-file>\n"
