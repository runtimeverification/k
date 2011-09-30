{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Distribution.Desk.Parser 
    ( parseDeskFile
    ) where

import Control.Applicative ((<$>))
import Control.Failure
import Control.Monad (join)
import Data.Object
import Data.Object.Yaml

import Distribution.Desk.Types hiding (getParser)

parseDeskFile :: FilePath -> IO Desk
parseDeskFile file = do
    input <- join $ decodeFile file
    desk <- yamlToDesk input
    return desk

yamlToDesk :: (Functor m, Failure ObjectExtractError m) => Object String String -> m Desk
yamlToDesk object = do
    fields <- fromMapping object
    name        <- getRequiredText "Name"        fields
    version     <- getRequiredText "Version"     fields
    license     <- getRequiredText "License"     fields
    synopsis    <- getRequiredText "Synopsis"    fields
    description <- getOptionalText "Description" fields
    authors     <- getRequiredText "Authors"     fields
    maintainer  <- getRequiredText "Maintainer"  fields
    tags        <- getOptionalText "Tags"        fields

    -- krun settings:
    sourceDir    <- getOptionalText "Source-dir" fields
    mainModule   <- getRequiredText "Main-module" fields
    syntaxModule <- getRequiredText "Syntax-module" fields
    parser       <- readParser <$> getRequiredText "Parser" fields
    outputMode   <- readOutputMode <$> getRequiredText "Output-mode" fields
    cellQuery    <- (case outputMode of
                        PrettyPrint -> getRequiredText
                        _           -> getOptionalText) "Cell-query" fields
    return $ Desk name version license synopsis description authors maintainer tags
                  sourceDir mainModule syntaxModule parser outputMode cellQuery


readParser "kast" = InternalKast
readParser _ = error "Support for external parser not implemented yet."

readOutputMode "io" = IOServer
readOutputMode "maude" = Maude
readOutputMode "pretty-print" = PrettyPrint

getRequiredText key pairs = lookupScalar key pairs

getOptionalText key pairs = do
    let maybeText = lookupScalar key pairs
    case maybeText of
        Nothing   -> return ""
        Just text -> return text
