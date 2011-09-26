module KRun.Types where

import Data.Text (Text)

-- | Type representing a flattened K term.
newtype Kast = Kast Text
    deriving Show

-- | Type representing uncompiled program source code.
newtype ProgramSource = ProgramSource Text
    deriving Show
