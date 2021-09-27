module TOKENCHECK-SYNTAX
  syntax X ::= "abc" [token]

endmodule

module TOKENCHECK
  imports TOKENCHECK-SYNTAX
  imports INT

  syntax X ::= fail()

  syntax Y ::= "a" [token]
  syntax Y ::= Z
  syntax Z ::= "b" [token]

  syntax Int ::= "foo"
  rule foo => 3 [macro]

endmodule
