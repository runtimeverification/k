requires "domains.md"

module SIMPLE-PROOFS
    imports INT
    imports MAP
    imports BOOL

    configuration <k> $PGM:KItem </k>
                  <state> .Map </state>

    syntax Bool ::= pred1 ( Int ) [function, functional, klabel(pred1), symbol, no-evaluators]
    syntax KItem ::= "foo" | "bar"

    syntax Foo ::= foo ( Bar ) [klabel(foo), symbol]

    syntax Bar ::= Baz

    syntax Baz ::= "foo-bar" | "baz" [klabel(baz), symbol]

    rule <k> foo => bar ... </k>
         <state> ... 3 |-> N ... </state>
      requires pred1(N)

endmodule
