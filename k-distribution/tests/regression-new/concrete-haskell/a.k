// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module A-SYNTAX
imports DOMAINS-SYNTAX
syntax Pgm ::= run(Int)
endmodule

module A
imports DOMAINS
imports A-SYNTAX
configuration <k> $PGM:Pgm </k> <counter> 0 </counter>

syntax Int ::= final(Int) [function, total]
             | "n" [function, total, no-evaluators]

rule <k> run(0) => .K </k> <counter> N:Int => final(N) </counter>
rule <k> run(N:Int => N -Int 1) ...</k> <counter> M:Int => M +Int 1 </counter>
    requires N >Int 0 andBool N %Int 2 ==Int 0
rule <k> run(N:Int => N -Int 1) ...</k> <counter> M:Int => 1 +Int M </counter>
    requires N >Int 0 andBool N %Int 2 ==Int 1

endmodule
