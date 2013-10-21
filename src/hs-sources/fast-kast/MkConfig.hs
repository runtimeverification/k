import Text.XML.HaXml
import Text.XML.HaXml.Util
import Text.XML.HaXml.Pretty
import Text.XML.HaXml.Posn
import Text.XML.HaXml.Wrappers

main = process "config.xml"
  "../../tests/config-orig.xml"
  "../../tests/config-new.xml"

{- Add a --parser=kast.sh option to all tests in a config file. -}
process name inFile outFile =
   readFile inFile >>= writeFile outFile . show . document . onContent processTests . xmlParse name

processTests = chip (doTest `when` tagWith (=="test"))

doTest = (tagWith (=="all-programs") `o` children)
  ?> chip (addChild useKast `when` tagWith (=="all-programs"))
  :> addChild (mkElem "all-programs" (useKast:defaultOptions))

addChild c = inplace (c `union` children)

krunOption opt val = 
  mkElemAttr "krun-option" [("name",literal opt),("value",literal val)] []
  
useKast = krunOption "--parser" "kast.sh"

defaultOptions =
  [krunOption "--no-color" ""
  ,krunOption "--output-mode" "none"]

instance Show (Content i) where
  show = show . content
