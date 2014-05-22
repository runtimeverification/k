// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax KItem ::= "test"
  rule test => !X:Int
  rule (. => !X:Id) ~> _:Int
endmodule

