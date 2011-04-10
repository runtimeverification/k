-- A simple frontend to the parser.
import Language.K.Parser.Parsec
import Text.Parsec (parse)

parseK :: String -> String
parseK s = (++"\n") . either show id $ parse kterm "" s

main :: IO ()
main = interact parseK
