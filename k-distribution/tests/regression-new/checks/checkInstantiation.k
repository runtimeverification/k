module CHECKMINTLITERAL-SYNTAX
  imports MINT-SYNTAX
endmodule

module CHECKMINTLITERAL
  imports CHECKMINTLITERAL-SYNTAX
  imports MINT

  syntax KItem ::= foo(MInt{6})

endmodule
