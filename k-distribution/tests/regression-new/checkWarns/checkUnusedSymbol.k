module CHECKUNUSEDSYMBOL-SYNTAX

endmodule

module CHECKUNUSEDSYMBOL
  imports CHECKUNUSEDSYMBOL-SYNTAX
  imports INT

  syntax Foo ::= foo(Int)
endmodule
