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
    -- krun settings:
    , sourceDir    :: FilePath
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
getSyntaxModule (Desk { syntaxModule = synMod }) = synMod

getMainModule :: Desk -> String
getMainModule (Desk { mainModule = mainMod }) = mainMod

getParser :: Desk -> Parser
getParser (Desk { parser = p }) = p

getOutputMode :: Desk -> OutputMode
getOutputMode (Desk { outputMode = om }) = om

getCellQuery :: Desk -> String
getCellQuery (Desk { cellQuery = cq }) = cq
