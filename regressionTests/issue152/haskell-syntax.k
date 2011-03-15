/*
    Definition of Haskell's abstract syntax in K, as based off of Language.Haskell.Exts.Syntax
*/

load ../../pl-builtins
load ../../k-prelude

kmod HASKELL-SYNTAX is
    including PL-STRING
    including K

    syntax K ::= Literal
               | Exp
               | Int

    syntax Literal ::= `Int K

    syntax Exp ::=  `Lit K
                 | `NegApp K


endkm
