// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
  imports DOMAINS-SYNTAX
  syntax Pgm ::= run(Int)
endmodule

module TEST
  imports DOMAINS
  imports TEST-SYNTAX
  configuration <k> $PGM:Pgm </k> <counter> 0 </counter> <mem> .Map </mem>

  syntax Int ::= final(Int) [function, total]
               | "n" [function, total, no-evaluators]
  syntax S ::= "notAFunction" | Int
             | "a" | "b" | "c"

  rule <k> run(0) => .K </k> <counter> N:Int => final(N) </counter>
  rule <k> run(N:Int => N -Int 1) ...</k> <counter> M:Int => M +Int 1 </counter>
      requires N >Int 0 andBool N %Int 2 ==Int 0
  rule <k> run(N:Int => N -Int 1) ...</k> <counter> M:Int => 1 +Int M </counter>
      requires N >Int 0 andBool N %Int 2 ==Int 1

  rule <k> a => b </k> <mem> MEM => MEM [ 3 <- 5 ] </mem>
  rule c => 2
endmodule
