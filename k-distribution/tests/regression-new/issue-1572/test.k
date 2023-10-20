// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
  imports ML-SYNTAX

  syntax KItem ::= "foo" [unused]

endmodule

module TEST
  imports TEST-SYNTAX

endmodule
