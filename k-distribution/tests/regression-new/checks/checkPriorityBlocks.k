module CHECKPRIORITYBLOCKS
  imports INT

  syntax Exp ::= Int
             | "[" Exp "]" [bracket, applyPriority(1)]
             > Exp "+" Exp
  rule [1 + 2] => .K
endmodule
