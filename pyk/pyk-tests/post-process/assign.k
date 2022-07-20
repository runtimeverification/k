module ASSIGN-SYNTAX
    imports INT-SYNTAX
    imports ID-SYNTAX

    syntax Expr ::= Int | Id

    syntax Stmt   ::= Decl | Assign
    syntax Decl   ::= "var" Ids ";"
    syntax Ids    ::= List{Id, ","}
    syntax Assign ::= Id "=" Expr ";" [strict(2)]

    syntax Pgm    ::= List{Stmt, ""}

    syntax KResult ::= Int
endmodule


module ASSIGN
    imports ASSIGN-SYNTAX
    imports BOOL

    configuration
        <T>
            <k> $PGM:Pgm </k>
            <env> .Map </env>
        </T>

    rule <k> S:Stmt P:Pgm => S ~> P ... </k>
    rule <k> .Pgm => . ... </k>

    rule [r1]: <k> X:Id => I ... </k>
               <env> ... X |-> I ... </env>

    rule [r2]: <k> X = I:Int; => . ... </k>
               <env> ... X |-> (_ => I) ... </env>

    rule <k> var .Ids ; => . ... </k>

    rule [r3]: <k> var (X, Xs => Xs); ... </k>
               <env> Rho:Map (.Map => X |-> 0) </env> requires notBool (X in_keys(Rho))
endmodule
