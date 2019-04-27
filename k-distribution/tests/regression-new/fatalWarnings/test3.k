module TEST3-SYNTAX

endmodule

module TEST3
  imports TEST3-SYNTAX
  imports BOOL

  syntax Bool ::= "foo" [function]

  rule 0 => 1
    requires (foo andBool (foo orBool foo) orBool foo)
endmodule
