module TEST
  imports STRING

  syntax KItem ::= foo(X)

  syntax X ::= String [klabel(bar)]
  syntax X ::= "<" String ">"

  rule T:String => < T > [anywhere]

  configuration <k> foo($PGM:String) </k>
endmodule

module TEST-SYNTAX
  imports TEST
endmodule
