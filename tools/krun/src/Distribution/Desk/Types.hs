module Distribution.Desk.Types where

data Desk = Desk
    { pkgName     :: String
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
    , outputMode   :: OutputMode
    , cellQuery    :: String
    } deriving Show

data Parser
    = InternalKast
    | External { command :: String }
    deriving Show

data OutputMode
    = IOServer
    | Maude
    | PrettyPrint
    deriving Show

-- Accessors

getSyntaxModule :: Desk -> String
getSyntaxModule (Desk { langInfo = LanguageInfo { syntaxModule = synMod } }) = synMod

getMainModule :: Desk -> String
getMainModule (Desk { langInfo = LanguageInfo { mainModule = mainMod } }) = mainMod

getParser :: Desk -> Parser
getParser (Desk { langInfo = LanguageInfo { parser = p } }) = p

getOutputMode :: Desk -> OutputMode
getOutputMode (Desk { langInfo = LanguageInfo { outputMode = om } }) = om

getCellQuery :: Desk -> String
getCellQuery (Desk { langInfo = LanguageInfo { cellQuery = cq } }) = cq
