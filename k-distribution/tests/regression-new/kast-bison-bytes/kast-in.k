// Copyright (c) 2019 K Team. All Rights Reserved.

module KAST-IN-SYNTAX
  imports BYTES-SYNTAX

  syntax Pgm ::= Bytes
endmodule

module KAST-IN
  imports KAST-IN-SYNTAX
  configuration <k> $PGM:Pgm </k>
endmodule
