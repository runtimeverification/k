/*
    Definition of Haskell's abstract syntax in K, as based off of Language.Haskell.Exts.Syntax
*/



module HASKELL-SYNTAX

    syntax K ::= Literal
               | Exp
               | Int

    syntax Literal ::= "Int" K

    syntax Exp ::=  "Lit" K
                 | "NegApp" K


end module
