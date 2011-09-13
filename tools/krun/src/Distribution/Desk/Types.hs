module Distribution.Desk.Types where

data Desk = Desk
    { name        :: String
    , version     :: String
    , license     :: String
    , synopsis    :: String
    , description :: String
    , authors     :: String
    , maintainer  :: String
    , tags        :: String
    , langInfo    :: LanguageInfo
    } deriving Show

data LanguageInfo = LanguageInfo
    { sourceDir    :: FilePath
    , mainModule   :: String
    , syntaxModule :: String
    , parser       :: Parser
    } deriving Show

data Parser
    = DefaultKast
        { programSort :: String }
    | External
        { command :: String }
    deriving Show


-- Accessors

getProgramSort :: Desk -> String
getProgramSort (Desk { langInfo = LanguageInfo { parser = DefaultKast sort } }) = sort

getSyntaxModule :: Desk -> String
getSyntaxModule (Desk { langInfo = LanguageInfo { syntaxModule = synMod } }) = synMod

getMainModule :: Desk -> String
getMainModule (Desk { langInfo = LanguageInfo { mainModule = mainMod } }) = mainMod

getParser :: Desk -> Parser
getParser (Desk { langInfo = LanguageInfo { parser = p } }) = p
