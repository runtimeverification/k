// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module A
  imports INT
  syntax Int ::= abs(Int) [function, total]
               | "error" [function, total]
  rule abs(X:Int) => X:Int requires X >Int 0
  rule abs(X) => 0 -Int X [owise]

  rule abs(0) => error [simplification]

  configuration <k> $PGM:Int </k>
endmodule
