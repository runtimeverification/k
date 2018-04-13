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
rule fff(2) => foo(inc(sym(?X:Int)))

rule run(2) => foo(inc(sym(222)))

rule run(3) => foo(inc(333))

syntax Int ::= sym(Int) [function]
             | sym2(Int)
rule sym(I) => sym2(I)

syntax Int ::= inc(Int) [function]
rule inc(I) => I +Int 1 [concrete]

syntax Int ::= foo(Int) [function]
rule foo(I) => I

endmodule
