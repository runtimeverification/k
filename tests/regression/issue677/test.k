module TEST
  syntax B ::= Int | B "*" B
   syntax A ::= B [klabel('a), strict]
		| A "+" A [strict]
		| print(A) [strict]

  syntax KResult ::= Int

  configuration <out stream="stdout"> .List </out> <k> $PGM:A </k>

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int + I2:Int => I1 +Int I2
  rule 'a(I:Int) => I

  rule <k> print(I:Int) => . ...</k> <out>... . => ListItem(I) </out>
endmodule
