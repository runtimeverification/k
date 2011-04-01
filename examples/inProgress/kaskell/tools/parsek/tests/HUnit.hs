-- HUnit test cases for the K parser.
-- Add more tests later.
import Control.Monad (when)
import System.Exit (exitFailure)
import Test.HUnit
import Text.Parsec (parse)

import Language.K

main :: IO ()
main = do
    counts <- runTestTT tests
    when (errors counts + failures counts > 0) exitFailure

tests :: Test
tests = TestList
    [ test001 `shouldParseTo` test001R
    , test002 `shouldParseTo` test002R
    , test003 `shouldParseTo` test003R
    ]

shouldParseTo :: String -> String -> Test
shouldParseTo input expected = TestCase (assertParse input expected)

assertParse :: String -> String -> Assertion
assertParse input expected = do
    case parse kterm "" input of
        Left error   -> assertFailure $
            input ++ " failed to parse: " ++ show error
        Right result -> assertEqual input expected result

test001  = "'NegApp_('Lit_('Int_(Int 42(.List{K}))))"
test001R = "NegApp (Lit (Int (42)))"

test002  = "'Lit_('String_(String \"hello\"(.List{K})))"
test002R = "Lit (String (\"hello\"))"

test003  = "'Let__('BDecls_('`(:`)__('FunBind_('`(:`)__('Match______('SrcLoc___(String \"unknown.hs\"(.List{K}),,Int 0(.List{K}),,Int 0(.List{K})),,'Ident_(String \"ok0\"(.List{K})),,'`(:`)__('PVar_('Ident_(String \"x\"(.List{K}))),,'`[`](.List{K})),,'Nothing(.List{K}),,'UnGuardedRhs_('Var_('UnQual_('Ident_(String \"foo\"(.List{K}))))),,'BDecls_('`[`](.List{K}))),,'`(:`)__('Match______('SrcLoc___(String \"unknown.hs\"(.List{K}),,Int 0(.List{K}),,Int 0(.List{K})),,'Ident_(String \"ok0\"(.List{K})),,'`(:`)__('PWildCard(.List{K}),,'`[`](.List{K})),,'Nothing(.List{K}),,'UnGuardedRhs_('App__('Var_('UnQual_('Ident_(String \"fail\"(.List{K})))),,'Lit_('String_(String \"pattern fail\"(.List{K}))))),,'BDecls_('`[`](.List{K}))),,'`[`](.List{K})))),,'`[`](.List{K}))),,'InfixApp___('Var_('UnQual_('Ident_(String \"xs\"(.List{K})))),,'QVarOp_('UnQual_('Symbol_(String \">>=\"(.List{K})))),,'Var_('UnQual_('Ident_(String \"ok0\"(.List{K}))))))"
test003R = "Let (BDecls ((:) (FunBind ((:) (Match (SrcLoc (\"unknown.hs\") (0) (0)) (Ident (\"ok0\")) ((:) (PVar (Ident (\"x\"))) ([])) (Nothing) (UnGuardedRhs (Var (UnQual (Ident (\"foo\"))))) (BDecls ([]))) ((:) (Match (SrcLoc (\"unknown.hs\") (0) (0)) (Ident (\"ok0\")) ((:) (PWildCard) ([])) (Nothing) (UnGuardedRhs (App (Var (UnQual (Ident (\"fail\")))) (Lit (String (\"pattern fail\"))))) (BDecls ([]))) ([])))) ([]))) (InfixApp (Var (UnQual (Ident (\"xs\")))) (QVarOp (UnQual (Symbol (\">>=\")))) (Var (UnQual (Ident (\"ok0\")))))"
