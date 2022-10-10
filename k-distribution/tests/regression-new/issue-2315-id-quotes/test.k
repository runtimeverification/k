module TEST 
  imports ID
  imports BOOL
  imports K-EQUAL
  imports STRING

  syntax Bool ::= "test" [function]

  // Evaluates to true
  rule test => String2Id("x") ==K #token("\"x\"", "Id")
endmodule
