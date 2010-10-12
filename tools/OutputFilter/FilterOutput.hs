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
  import Control.Applicative hiding (empty)
  import Control.Monad
  import Control.Monad.Identity
  import Control.Monad.State
  import Control.Monad.List
  import Data.List
  import Data.Maybe

  -- Strip off surrounding whitespaces, remove empty strings, remove those blasted DOS carriage returns
  cleanupStrings :: [KOutput] -> [KOutput]
  cleanupStrings = remEmpty . map stripStrs
    where stripStrs (String s) = String (stripr (deleteAll '\r' s))
          stripStrs x = x
          remEmpty (String "" : xs) = remEmpty xs
          remEmpty (x:xs) = x : remEmpty xs
          remEmpty [] = []

  -- Delete all occurances
  deleteAll :: Eq a => a -> [a] -> [a]
  deleteAll x = filter ((/=) x)

  {-
    Pretty Printing
   -}

  ppBeginCell :: String -> Doc
  ppBeginCell n = text $ "< " ++ n ++ " >"

  ppEndCell :: String -> Doc
  ppEndCell n = text $ "</ " ++ n ++ " >"

  ppKOutput :: Configuration -> KOutput -> Doc
  ppKOutput conf (String s) = text s
  ppKOutput conf (Cell name contents) | shouldShow conf name = linebreak <> (hang 1 $ ppBeginCell name
                                                                         <> handleContents contents
                                                                        <+> ppEndCell name)
                                      | shouldRecHide conf name = empty
                                      | otherwise            = handleContents $ filter isCell contents

    where handleContents cs = (hcat . map (ppKOutput conf) . pruneStrings conf name . cleanupStrings) cs


  isCell (Cell _ _) = True
  isCell _          = False

  isString (String _ ) = True
  isString _           = False



  -- Prune off lines after the user-specified break
  pruneStrings :: Configuration -> CellName -> [KOutput] -> [KOutput]
  pruneStrings conf cn ks | shouldPrune conf cn = map (prune conf cn) (filter isString ks)
                          | otherwise           = ks


  prune conf cn (String s) = String $ (stripr . unlines . take toKeep) intermediate ++ more
    where toKeep = getPruneNumber conf cn
          intermediate = lines s
          more = " [..." ++ show (length intermediate - 1) ++ " more...]"






  -- Lookup the config for the cell
  lookupCell :: Configuration -> CellName -> Maybe CellConfigRhs
  lookupCell conf cn = snd <$> find ((cn ==) . fst) conf

  -- Should a cell be shown?
  shouldShow :: Configuration -> CellName -> Bool
  shouldShow conf cn = case lookupCell conf cn of
                         Just Hide          -> False
                         Just RecursiveHide -> False
                         Nothing            -> False
                         _                  -> True

   -- Should a cell be recursively hidden?
  shouldRecHide :: Configuration -> CellName -> Bool
  shouldRecHide conf cn = case lookupCell conf cn of
                            Just RecursiveHide -> True
                            _                  -> False


  -- Should a cell be pruned?
  shouldPrune :: Configuration -> CellName -> Bool
  shouldPrune conf cn = case lookupCell conf cn of
                          Just (Configs (Just _) _ _) -> True
                          _                           -> False


  -- Fetch the number of lines to keep from the configuration
  getPruneNumber :: Configuration -> CellName -> Int
  getPruneNumber conf cn = case lookupCell conf cn >>= keepLines of
                             Just n -> n
                             _      -> error "internal error: shouldPrune approved a prune candidate incorrectly"

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
                       _   -> error "Use like this: runhaskell <prog> <outputfile> <configfile>"
            parsedOut <- parseKOutFile fname
            config <- getConfig configFile
            putStrLn . stringifyDoc . cat . map (ppKOutput config) $ parsedOut
