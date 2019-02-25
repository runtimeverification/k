module TEST
  imports INT
  imports BOOL

  syntax KItem ::= "foo" | "bar" | "baz"
  rule foo #Or bar #Or baz => 0

endmodule
