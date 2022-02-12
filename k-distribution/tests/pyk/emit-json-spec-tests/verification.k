requires "imp.k"

module VERIFICATION-SYNTAX
    syntax Id ::= "$s" [token]
                | "$n" [token]
endmodule

module VERIFICATION
    imports VERIFICATION-SYNTAX
    imports IMP

    syntax Bool ::= pred1 ( Int ) [function, functional, klabel(pred1), symbol, no-evaluators]
    syntax KItem ::= "foo" | "bar"

    rule <k> foo => bar ... </k>
         <state> ... $n |-> N ... </state>
      requires pred1(N)

endmodule

