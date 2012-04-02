module INTLABEL 

    syntax K ::= Exp | Int | "pgm"

    syntax Exp ::= "Lit" Literal
                 | "foo"

    syntax Literal ::= "Int" Int

    macro Lit (Int I:Int) = foo

end module
