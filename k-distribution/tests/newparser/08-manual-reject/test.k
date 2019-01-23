// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST
  syntax AA ::= Token{[\$][a]*[b][c]*} [token, regex("[$][a]*[b][a]*"), reject2("$b")]
  syntax AA ::= "$b" [reject]

  syntax BB ::= Token{[\$][b-z]+}  [token, regex("[$][b-z]+")]
  syntax CC ::= AA | BB
  configuration <k> $PGM:CC </k>
  rule X:BB => .K
endmodule
