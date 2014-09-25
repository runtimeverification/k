// Copyright (c) 2014 K Team. All Rights Reserved.
module TEST
  syntax AA ::= Token{[\$][a]*[b][c]*} [regex("[$][a]*[b][a]*")]
  syntax AA ::= "$b" [reject]

  syntax BB ::= Token{[\$][b-z]+}  [regex("[$][b-z]+")]
  syntax CC ::= AA | BB
  configuration <k> $PGM:CC </k>
  rule X:BB => .K
endmodule
