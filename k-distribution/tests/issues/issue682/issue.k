// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE
  syntax KItem ::= "foo"

  configuration <k> foo </k>

  rule _:KItem => .
endmodule

