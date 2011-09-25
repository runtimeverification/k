module KRun.XPath
    ( xpath
    ) where

import Text.XML.HXT.Core
import Text.XML.HXT.XPath

-- TODO: switch back to using runX/IO?
xpath :: String -> String -> [String]
xpath query xmlstr = runLA
        --readString [] xmlstr
        (xread
        >>>
        getXPathTrees query
        >>>
        -- Is this the best thing to do?
        xshow this) xmlstr
