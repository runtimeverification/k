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
  handleContents conf name cs = hcat $ (map (ppKOutput conf) . pruneStrings conf name . cleanupStrings)  cs


  handleString :: KOutPrinter
  handleString conf (String n s) = text s
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
  handleStyle conf name f doc | hasStyle conf name f = stylize (fetchStyle conf name f) doc
                              | otherwise            = doc

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
  colorize c p = id

  -- Prune off lines after the user-specified break
  pruneStrings :: Configuration -> CellName -> [KOutput] -> [KOutput]
  pruneStrings conf cn ks | shouldPrune conf cn = map (prune conf cn) (filter isString ks)
                          | otherwise           = ks


  prune conf cn (String n s) = String n $ (stripr . unlines . take toKeep) intermediate ++ more
    where toKeep = fetchPruneNumber conf cn
          intermediate = lines s
          more = " [..." ++ show (length intermediate - 1) ++ " more...]"




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
                          Just (Configs (Just _) _ _) -> True
                          _                           -> False

  hasStyle :: StyleReader Bool
  hasStyle conf cn f = case lookupCell conf cn of
                           Just c@(Configs _ _ _) -> isJust (f c)
                           _                      -> False

  fetchStyle :: StyleReader Style
  fetchStyle conf cn f = case lookupCell conf cn >>= f of
                         Just s -> s
                         _      -> error "Internal Error: hasStyle approved a cell incorrectly"

  -- Fetch the number of lines to keep from the configuration
  fetchPruneNumber :: CellReader Int
  fetchPruneNumber conf cn = case lookupCell conf cn >>= keepLines of
                             Just n -> n
                             _      -> error "Internal Error: shouldPrune approved a prune candidate incorrectly"

  -- Whether a maybe is something

  -- Convert to string
  stringifyDoc :: Doc -> String
  stringifyDoc doc = tail $ (displayS $ renderPretty 1.0 80 doc) ""


  -- Todo: implement real argument parsing, and real error handling
  main :: IO ()
  main = do args <- getArgs
            (fname, configFile) <- case args of
                       (x:y:xs) -> return (x,y)
                       -- []  -> error "Please specify a file to filter"
                       _   -> error usage
            parsedOut <- parseKOutFile fname
            config <- getConfig configFile
            putStrLn . stringifyDoc . cat . map (ppKOutput config) $ parsedOut

  usage = "\nUsage:\n" ++ "  If you have built the tool using 'make', then run:\n"
                     ++ "    filterOutput <output-file> <yaml-config-file>\n"
                     ++ "  To run the tool without building it, run:\n"
                     ++ "    runhaskell FilterOutput.hs <output-file> <yaml-config-file>\n"
