// Copyright (c) 2020 K Team. All Rights Reserved.
// This is temporary to test if kprove gives a warning when it finds rules in a specification
// once the transition to claim is done, it should be removed

module WARNCLAIM-SYNTAX
    imports INT

    syntax Int ::= "foo" [macro]
    rule foo => 3

    syntax Pgm ::= doIt ( Int )
    syntax Pgm ::= addCounter ( Int )
endmodule

module WARNCLAIM
    imports WARNCLAIM-SYNTAX

    configuration <k> $PGM:Pgm </k> <counter> 1 </counter> <sum> 0 </sum>

    rule <k> addCounter(0) => . ... </k>
    rule  <k> addCounter(Times:Int => Times -Int 1) ...</k>
          <counter> C:Int => C +Int 1 </counter>
          <sum> S:Int => S +Int C </sum>
      requires Times >Int 0

    rule <k> doIt(I => I -Int 1) ... </k> requires I >Int 0
endmodule
