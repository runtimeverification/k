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

  rule foo(X) => 0
    requires X >Int 0
  rule foo(X) => 1
    requires 0 >Int 0

  rule foo(X) => ?X:Int
    ensures X >Int 0

  configuration <k> $PGM:K </k> <foo multiplicity="?"> <bar/> </foo>

endmodule
