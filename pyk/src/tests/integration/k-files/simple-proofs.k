requires "domains.md"

module SIMPLE-PROOFS
    imports INT
    imports MAP
    imports BOOL
    imports BYTES

    configuration <k> $PGM:KItem </k>
                  <state> .Map </state>

    syntax Bool ::= pred1 ( Int ) [function, total, klabel(pred1), symbol, no-evaluators]
    syntax KItem ::= "foo" | "bar"

    syntax Foo ::= foo ( Bar ) [klabel(foo), symbol]

    syntax Bar ::= Baz

    syntax Baz ::= "foo-bar" | "baz" [klabel(baz), symbol]

    syntax BarHolder ::= hold ( Foo , Bar ) [klabel(barholder), symbol]
                       | hold2 ( Bar , Baz ) [klabel(barholder2), symbol]

    rule [foo-to-bar]:
         <k> foo => bar ... </k>
         <state> ... 3 |-> N ... </state>
      requires pred1(N)

    rule [foo-to-bar-false]:
         <k> (foo => bar) ~> _RestK </k>
         <state> (3 |-> N) _RestState </state>
      requires pred1(N) andBool false
      [priority(30)]

    rule [foo-to-baz-owise]:
         <k> foo ~> foo ~> foo => baz ~> foo ~> foo ...</k> [owise]

    syntax KItem ::= Step
    syntax Step ::= "a" | "b" | "c" | "d" | "e"

    rule [a.b]: <k> a => b ... </k>
    rule [b.c]: <k> b => c ... </k>
    rule [b.d]: <k> b => d ... </k>
    rule [c.e]: <k> c => e ... </k>
    rule [d.e]: <k> d => e ... </k>

    syntax KItem ::= "mybytes" [symbol, klabel(mybytes), function, total]
    rule mybytes => b"\x00\x90\xa0\n\xa1\xf1\x61"

    syntax Foo ::= abcd(K) [klabel(abcd), symbol]

endmodule
