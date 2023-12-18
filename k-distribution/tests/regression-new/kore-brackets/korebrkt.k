// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module KOREBRKT-SYNTAX
  imports INT

  syntax {Sort} Sort ::= "[" Sort "]" [bracket]
endmodule

module KOREBRKT
  imports KOREBRKT-SYNTAX

  configuration <k color="green"> $PGM:Int </k>
endmodule
