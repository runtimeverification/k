requires "domains.md"

module SIMPLE-PROOFS
    imports INT
    imports MAP
    imports BOOL
    imports BYTES

    configuration <k> $PGM:KItem </k>
                  <state> .Map </state>

    syntax Bool ::= pred1 ( Int ) [function, total, symbol(pred1), no-evaluators]
    syntax KItem ::= "foo" | "bar"

    syntax Foo ::= foo ( Bar ) [symbol(foo)]

    syntax Bar ::= Baz

    syntax Baz ::= "foo-bar" | "baz" [symbol(baz)]

    syntax BarHolder ::= hold ( Foo , Bar ) [symbol(barholder)]
                       | hold2 ( Bar , Baz ) [symbol(barholder2)]

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
    syntax Step ::= "a" | "b" | "c" | "d" | "e" | "f"

    rule [a.b]: <k> a => b ... </k>
    rule [b.c]: <k> b => c ... </k>
    rule [b.d]: <k> b => d ... </k>
    rule [c.e]: <k> c => e ... </k>
    rule [d.e]: <k> d => e ... </k>
    rule [e.f]: <k> e => f ... </k>

    syntax KItem ::= "mybytes" [symbol(mybytes), function, total]
    rule mybytes => b"\x00\x90\xa0\n\xa1\xf1\x61"

    syntax Foo ::= abcd(K) [symbol(abcd)]

    syntax Int ::= simpleFunction() [symbol(simpleFunc), function, total]
                 | leqZero(Int) [symbol(leqZero), function, total]
                 | leq(Int, Int) [symbol(leq), function, total, smtlib(leq)]
    rule leq(_,_) => 0
    rule [simple-func]: simpleFunction() => 3
    rule [simple-func-req-1]: leqZero(X) => 0 requires X <=Int 0
    rule [simple-func-req-2]: leqZero(X) => 1 requires 0 <Int X
    rule [simple-func-simplification]: leqZero(X) => 1 requires 0 <Int X [simplification]
    rule [simple-func-simplification-prio]: leqZero(X) => 1 requires 0 <Int X [simplification(38)]
    rule [simple-func-simplification-concrete-noarg]: leqZero(X) => 1 requires 0 <Int X [simplification, concrete]
    rule [simple-func-simplification-concrete]: leqZero(X) => 1 requires 0 <Int X [simplification, concrete(X)]
    rule [simple-func-simplification-symbolic]: leqZero(X) => 1 requires 0 <Int X [simplification, symbolic(X)]
    rule [simple-func-simplification-symbolic-2vars]: leq(X,_Y) => 1 requires 0 <Int X [simplification, symbolic(X,_Y)]
    rule [simple-func-simplification-smt-lemma]: leq(_,_) ==Int 0 => false [simplification, smt-lemma]

endmodule
