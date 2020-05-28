module CHECKUNUSEDVAR-SYNTAX

endmodule

module MOD
  imports INT
  configuration <bar> 0 </bar>
endmodule

module CHECKUNUSEDVAR
  imports INT
  imports MOD

  syntax KItem ::= foo(Int)

  rule foo(X) => 0
  rule foo(0) => !_:Int

  configuration <k> $PGM:K </k> <foo multiplicity="?"> <bar/> </foo>

endmodule
