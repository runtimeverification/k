module GHC-CORE-TEST-SYNTAX

    syntax Aexp ::= Qvar
                  | "(" Exp ")"

    syntax Vdefg ::= Vdef

    syntax Vdef ::= Qvar "::" Ty "=" Exp

    syntax Exp ::= Aexp
                 | Aexp Aexp
                 | "%let" Vdefg "%in" Exp

    syntax Aty ::= Tyvar

    syntax Bty ::= Aty

    syntax Ty ::= Bty
                | Bty "->" Ty

    syntax Tyvar ::= "tv(" Id ")"
    syntax Qvar ::= "qv(" Id ")"

end module

module GHC-CORE-TEST 
    imports GHC-CORE-TEST-SYNTAX
end module
