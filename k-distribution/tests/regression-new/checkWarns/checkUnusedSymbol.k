module CHECKUNUSEDSYMBOL-SYNTAX

endmodule

module CHECKUNUSEDSYMBOL
  imports CHECKUNUSEDSYMBOL-SYNTAX
  imports INT

  syntax Foo ::= foo(Int)

  syntax Bar ::= bar(Int) [unused]
endmodule
