// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports ID
  imports BOOL
  imports K-EQUAL
  imports STRING
  imports INT

  syntax Bool ::= "test"  [function]
                | "test2" [function]

  // Evaluates to true if the Id constructed by String2Id contains extra quotes
  rule test => String2Id("x") ==K #token("\"x\"", "Id")

  // Test that hooks producing a result of sort String are wrapped
  rule test2 => Int2String(2) ==K "2"
endmodule
