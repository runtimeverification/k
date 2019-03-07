// Copyright (c) 2019 K Team. All Rights Reserved.

requires "kast.k"

module KOREOUT-SYNTAX
  imports INT

  syntax Pgm ::= init ( Int )
endmodule

module KOREOUT
  imports KOREOUT-SYNTAX

  configuration <k color="green"> $PGM:Pgm </k>
endmodule
