// Copyright (c) 2019 K Team. All Rights Reserved.

requires "kast.k"

module EQ-SYNTAX
  imports KSEQ-SYMBOLIC
  imports INT

  syntax Pgm ::= KBott

  syntax Pgm ::= init ( Int )
endmodule

module EQ
  imports EQ-SYNTAX

  configuration <k color="green"> $PGM:Pgm </k>

  rule <k> init(0) => { 3 #Equals 4 } ... </k>
  rule <k> init(1) => { 3 #Equals 3 } ... </k>
endmodule
