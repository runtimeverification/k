// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module ISSUE-SYNTAX
  syntax SExps ::= List{SExp, " "}
  syntax SExp ::= Id | String // this is enough to reproduce the issue
endmodule

module ISSUE
  imports ISSUE-SYNTAX

  configuration <k> $PGM:K </k>



endmodule