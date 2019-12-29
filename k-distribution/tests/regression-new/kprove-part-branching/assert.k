// Copyright (c) 2019 K Team. All Rights Reserved.

module ASSERT
  imports BOOL
  imports INT

  configuration <T>
    <k> $PGM:K </k>
  </T>

  syntax Assert ::= "assert" Bool
  rule assert B => .
    requires B

endmodule
