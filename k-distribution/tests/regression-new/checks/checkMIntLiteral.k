module CHECKMINTLITERAL-SYNTAX
  imports MINT-SYNTAX
endmodule

module CHECKMINTLITERAL
  imports CHECKMINTLITERAL-SYNTAX
  imports MINT

  syntax MInt{6}
  syntax KItem ::= foo(MInt{6})

  rule foo(0p32) => 0

endmodule
