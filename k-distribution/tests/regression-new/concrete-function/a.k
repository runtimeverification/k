module A-SYNTAX
imports DOMAINS-SYNTAX
syntax Pgm ::= run(Int)
endmodule
module A
imports DOMAINS
imports A-SYNTAX
configuration <k> $PGM:Pgm </k>

syntax Pgm ::= fff(Int)
rule run(1) => fff(1)
rule fff(1) => fff(2)
rule fff(2) => foo(inc(sym(?_X:Int))) // terms with variables are not concrete

// sym(222) is a functional term, thus not concrete even if no variable appears, for which the inc rule is not applicable,
// but it will be rewritten to sym2(222), which is a normal (ground) term, and concrete.
rule run(2) => foo(inc(sym(222)))

rule run(3) => foo(inc(333))

syntax Num ::= Int
syntax Num ::= Num "+Num" Num [function]
rule I:Int +Num J:Int => I +Int J

syntax Num ::= sym(Int) [function]
             | sym2(Int)
rule sym(I) => sym2(I)

syntax Num ::= inc(Num) [function]
rule inc(I) => I +Num 1 [concrete]

syntax Num ::= foo(Num) [function]
rule foo(I) => I

// for testing `--concrete-rules` option

syntax Pgm ::= begin(Int) | end(Int)

rule begin(X) => end(X)

syntax Int ::= bar1(Int) [function, smtlib(bar1)]
             | bar2(Int) [function, smtlib(bar2)]
             | bar3(Int) [function, smtlib(bar3)]

rule [f1]: bar1(X) => bar2(X) requires X >Int 0

rule [f2]: bar1(X) => bar3(X) requires X <Int 0

endmodule
