module TEST
  imports ID
  imports BOOL
  imports K-EQUAL
  imports STRING

  syntax Bool ::= "test" [function]

  // Evaluates to true if the Id constructed by String2Id contains extra quotes
  rule test => String2Id("x") ==K #token("\"x\"", "Id")
endmodule
