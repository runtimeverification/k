// Copyright (c) 2019 K Team. All Rights Reserved.

module VAR-EQ

  configuration <T>
    <k> $PGM:K </k>
  </T>

  syntax ATerm ::= "a1" | "a2" | "a3"
  syntax BTerm ::= "b1" | "b2" | "b3"

  rule a1 => a2
  rule b1 => b2

endmodule
