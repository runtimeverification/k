// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE
  syntax KItem ::= "()"
  rule <k> '`(`)(.KList) => () ~> () </k>
endmodule

