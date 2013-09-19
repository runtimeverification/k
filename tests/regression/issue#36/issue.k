/*
Expected:
'L(res(X))
*/
module ISSUE
  configuration <k> 'L('A(.KList)) </k>

  syntax KLabel  ::= "'L" | "'A"
  syntax K ::= "dummy"
  syntax KResult ::= "res" "(" Id ")"
  context 'L(HOLE)
  rule 'A(_) => res(String2Id("X"))
endmodule
