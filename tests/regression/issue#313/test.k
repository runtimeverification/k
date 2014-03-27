module TEST
  syntax KLabel ::= "#foo"
  syntax K ::= foo(K)  [function, klabel(#foo)]
  rule #foo(1) => 0
endmodule
