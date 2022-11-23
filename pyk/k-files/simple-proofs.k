requires "domains.md"

module SIMPLE-PROOFS
    imports INT
    imports MAP
    imports BOOL

    configuration <k> $PGM:KItem </k>
                  <state> .Map </state>

    syntax Bool ::= pred1 ( Int ) [function, total, klabel(pred1), symbol, no-evaluators]
    syntax KItem ::= "foo" | "bar"

    syntax Foo ::= foo ( Bar ) [klabel(foo), symbol]

    syntax Bar ::= Baz

    syntax Baz ::= "foo-bar" | "baz" [klabel(baz), symbol]

    syntax BarHolder ::= hold ( Foo , Bar ) [klabel(barholder), symbol]
                       | hold2 ( Bar , Baz ) [klabel(barholder2), symbol]

    rule <k> foo => bar ... </k>
         <state> ... 3 |-> N ... </state>
      requires pred1(N)

    syntax KItem ::= Step
    syntax Step ::= "a" | "b" | "c" | "d" | "e"

    rule [a.b]: <k> a => b ... </k>
    rule [b.c]: <k> b => c ... </k>
    rule [b.d]: <k> b => d ... </k>
    rule [c.e]: <k> c => e ... </k>
    rule [d.e]: <k> d => e ... </k>

endmodule
