// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST
  imports INT
  imports BOOL
  imports ML-SYNTAX

  syntax KItem ::= "foo" | "bar" | "baz"
  rule foo #Or bar #Or baz => 0

endmodule
