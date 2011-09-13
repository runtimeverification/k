{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
module Distribution.Desk.Parser 
    ( parseDeskFile
    ) where

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

yamlToDesk :: (Failure ObjectExtractError m) => Object String String -> m Desk
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
    langInfo    <- getLanguageInfo fields
    return $ Desk name version license synopsis description authors maintainer tags langInfo

getLanguageInfo topFields = do
    fields <- lookupMapping "Language" topFields
    sourceDir    <- getRequiredText "Source-dir" fields
    mainModule   <- getRequiredText "Main-module" fields
    syntaxModule <- getRequiredText "Syntax-module" fields
    parser       <- getParser fields
    return $ LanguageInfo sourceDir mainModule syntaxModule parser

getParser langFields = do
    fields <- lookupMapping "Parser" langFields
    config <- getRequiredText "Config" fields
    case config of
        "default-kast" -> do
            programSort <- getRequiredText "Program-sort" fields
            return $ DefaultKast programSort
        "external" -> do
            command <- getRequiredText "Command" fields
            return $ External command
        -- TODO: better error handling.
        _ -> error "Invalid parser configuration."

getRequiredText key pairs = lookupScalar key pairs

getOptionalText key pairs = do
    let maybeText = lookupScalar key pairs
    case maybeText of
        Nothing   -> return ""
        Just text -> return text
