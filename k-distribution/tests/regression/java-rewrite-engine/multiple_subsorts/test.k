// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST
  syntax Sort ::= Int | Bool
  syntax KResult ::= Int | Bool
  syntax KItem ::= "test"
  rule test => isKResult(?S:Sort) ~> ?KR:KResult ==K ?S:Sort
endmodule
