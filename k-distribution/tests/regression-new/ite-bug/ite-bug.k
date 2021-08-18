// Copyright (c) 2019 K Team. All Rights Reserved.

module ITE-BUG-SYNTAX
    imports INT
    imports K-EQUAL
    imports BOOL

    syntax Pgm ::= Instr
    syntax Instr ::= "JUMPI" Int Int
    syntax Int ::= bool2Word ( Bool ) [function]

endmodule

module ITE-BUG
    imports ITE-BUG-SYNTAX

    configuration
      <k> $PGM:Pgm </k>
      <pc> 0 </pc>

    rule <k> JUMPI _DEST I => . ... </k>
         <pc> PCOUNT => PCOUNT +Int 1 </pc>
      requires I ==Int 0

    rule <k> JUMPI DEST I => . ... </k>
         <pc> _PCOUNT => DEST </pc>
      requires I =/=Int 0

    rule bool2Word( B:Bool ) => 1 requires B
    rule bool2Word( B:Bool ) => 0 requires notBool B

  rule bool2Word(A)  ==K 0 => notBool(A)  [simplification]
  rule bool2Word(A)  ==K 1 => A           [simplification]
  rule bool2Word(A)  =/=K 0 => A          [simplification]
  rule bool2Word(A)  =/=K 1 => notBool(A) [simplification]

endmodule
