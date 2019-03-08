// Copyright (c) 2019 K Team. All Rights Reserved.

module KOREPOLY-SYNTAX
  imports INT

  syntax Pgm ::= Int | init ( Int , Pgm ) [poly(0,2)]
endmodule

module KOREPOLY
  imports KOREPOLY-SYNTAX

  configuration <k color="green"> $PGM:Pgm </k>
endmodule
