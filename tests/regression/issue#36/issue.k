// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/*
Expected:
'L(res(X))
*/
module ISSUE
  configuration <k> 'L('A(.KList)) </k>

  syntax KLabel  ::= "'L" | "'A"
  syntax KItem ::= "dummy"
  syntax KResult ::= "res" "(" Id ")"
  context 'L(HOLE)
  rule 'A(_) => res(String2Id("X"))
endmodule
