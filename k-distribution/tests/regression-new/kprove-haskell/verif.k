// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module VERIF-SYNTAX
    imports INT

    syntax Int ::= "foo" [macro]
    rule foo => 3

    syntax Pgm ::= doIt ( Int )
    syntax Pgm ::= addCounter ( Int )
endmodule

module VERIF
    imports VERIF-SYNTAX

    configuration <k> $PGM:Pgm </k> <counter> 1 </counter> <sum> 0 </sum>

    rule <k> addCounter(0) => .K ... </k>
    rule  <k> addCounter(Times:Int => Times -Int 1) ...</k>
          <counter> C:Int => C +Int 1 </counter>
          <sum> S:Int => S +Int C </sum>
      requires Times >Int 0

    rule <k> doIt(I => I -Int 1) ... </k> requires I >Int 0
endmodule
