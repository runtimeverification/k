{-# LANGUAGE OverloadedStrings #-}
-- HUnit test cases for the K parser.
-- TODO: Add more tests later.
import Control.Monad (when)
import Data.Attoparsec.Char8 (parseOnly)
import Data.ByteString.Char8 (ByteString, unpack)
import Data.ByteString.Builder (toByteString)
import Data.String (IsString)
import System.Exit (exitFailure)
import Test.HUnit
import Text.Parsec (parse)

import qualified Language.K.Parser.Parsec as S
import qualified Language.K.Parser.Attoparsec as B

main :: IO ()
main = do
    counts <- runTestTT tests
    when (errors counts + failures counts > 0) exitFailure

tests :: Test
tests = TestList
    [ test001 `shouldParseToS` test001R
    , test002 `shouldParseToS` test002R
    , test003 `shouldParseToS` test003R
    -- Attoparsec tests
    , test001 `shouldParseToB` test001R
    , test002 `shouldParseToB` test002R
    , test003 `shouldParseToB` test003R
    ]

shouldParseToS :: String -> String -> Test
shouldParseToS input expected = TestCase (assertParsec input expected)

assertParsec :: String -> String -> Assertion
assertParsec input expected = do
    case parse S.kterm "" input of
        Left error   -> assertFailure $
            input ++ " failed to parse: " ++ show error
        Right result -> assertEqual input expected result

shouldParseToB :: ByteString -> ByteString -> Test
shouldParseToB input expected = TestCase (assertAttoparsec input expected)

assertAttoparsec :: ByteString -> ByteString -> Assertion
assertAttoparsec input expected = do
    let sinput = unpack input
    case parseOnly B.kterm input of
        Left error    -> assertFailure $
            sinput ++ " failed to parse: " ++ error
        Right builder -> assertEqual sinput expected result
            where result = toByteString builder

test001, test001R :: (IsString a) => a
test002, test002R :: (IsString a) => a
test003, test003R :: (IsString a) => a

test001  = "'NegApp_('Lit_('Int_(Int 42(.List{K}))))"
test001R = "NegApp (Lit (Int (42)))"

test002  = "'Lit_('String_(String \"hello\"(.List{K})))"
test002R = "Lit (String (\"hello\"))"

test003  = "'Let__('BDecls_('`(:`)__('FunBind_('`(:`)__('Match______('SrcLoc___(String \"unknown.hs\"(.List{K}),,Int 0(.List{K}),,Int 0(.List{K})),,'Ident_(String \"ok0\"(.List{K})),,'`(:`)__('PVar_('Ident_(String \"x\"(.List{K}))),,'`[`](.List{K})),,'Nothing(.List{K}),,'UnGuardedRhs_('Var_('UnQual_('Ident_(String \"foo\"(.List{K}))))),,'BDecls_('`[`](.List{K}))),,'`(:`)__('Match______('SrcLoc___(String \"unknown.hs\"(.List{K}),,Int 0(.List{K}),,Int 0(.List{K})),,'Ident_(String \"ok0\"(.List{K})),,'`(:`)__('PWildCard(.List{K}),,'`[`](.List{K})),,'Nothing(.List{K}),,'UnGuardedRhs_('App__('Var_('UnQual_('Ident_(String \"fail\"(.List{K})))),,'Lit_('String_(String \"pattern fail\"(.List{K}))))),,'BDecls_('`[`](.List{K}))),,'`[`](.List{K})))),,'`[`](.List{K}))),,'InfixApp___('Var_('UnQual_('Ident_(String \"xs\"(.List{K})))),,'QVarOp_('UnQual_('Symbol_(String \">>=\"(.List{K})))),,'Var_('UnQual_('Ident_(String \"ok0\"(.List{K}))))))"
test003R = "Let (BDecls ((:) (FunBind ((:) (Match (SrcLoc (\"unknown.hs\") (0) (0)) (Ident (\"ok0\")) ((:) (PVar (Ident (\"x\"))) ([])) (Nothing) (UnGuardedRhs (Var (UnQual (Ident (\"foo\"))))) (BDecls ([]))) ((:) (Match (SrcLoc (\"unknown.hs\") (0) (0)) (Ident (\"ok0\")) ((:) (PWildCard) ([])) (Nothing) (UnGuardedRhs (App (Var (UnQual (Ident (\"fail\")))) (Lit (String (\"pattern fail\"))))) (BDecls ([]))) ([])))) ([]))) (InfixApp (Var (UnQual (Ident (\"xs\")))) (QVarOp (UnQual (Symbol (\">>=\")))) (Var (UnQual (Ident (\"ok0\")))))"
