module A-SYNTAX
imports DOMAINS-SYNTAX
syntax Pgm ::= run(Int)
endmodule
module A
imports DOMAINS
imports A-SYNTAX
configuration <k> $PGM:Pgm </k> <counter> 0 </counter>

syntax Int ::= final(Int) [function, functional]

rule <k> run(0) => .K </k> <counter> N:Int => final(N) </counter>
rule <k> run(N:Int => N -Int 1) ...</k> <counter> M +Int 1 </counter>
    requires N >Int 0

rule final(N:Int +Int M:Int) => 0 [simplification, concrete(M), symbolic(N)]

rule X +Int (Y +Int Z) => (X +Int Y) +Int Z [simplification, concrete(X, Y), symbolic(Z)]

rule X +Int (Y +Int Z) => (X +Int Z) +Int Y [simplification, concrete(X), symbolic(Y), concrete(Z)]

endmodule
