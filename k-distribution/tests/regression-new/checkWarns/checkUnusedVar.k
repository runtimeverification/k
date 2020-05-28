module CHECKUNUSEDVAR-SYNTAX

endmodule

module CHECKUNUSEDVAR
  imports INT

  syntax KItem ::= foo(Int)

  rule foo(X) => 0
  rule foo(0) => !_:Int

endmodule
