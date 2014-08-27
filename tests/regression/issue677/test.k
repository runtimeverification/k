// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module TEST-SYNTAX
  syntax B ::= Int | B "*" B
   syntax A ::= B [klabel('a), strict]
        | A "+" A [strict]
        | print(A) [strict]

endmodule

module TEST
  imports TEST-SYNTAX
  syntax A ::= Int

  syntax KResult ::= Int

  configuration <out stream="stdout"> .List </out> <k> $PGM:A </k>

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule 'a(I:Int) => I

  rule <k> print(I:Int) => . ...</k> <out>... .List => ListItem(I) </out>
endmodule
