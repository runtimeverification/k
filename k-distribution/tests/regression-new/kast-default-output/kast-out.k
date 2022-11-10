// Copyright (c) 2019 K Team. All Rights Reserved.

module KAST-OUT-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX

  syntax Pgm ::= init ( Int ) [macro]
  rule init(0) => { 3 #Equals 4 }
  rule init(1) => { 3 #Equals 3 }
endmodule

module KAST-OUT
  imports KAST-OUT-SYNTAX
  configuration <k color="green"> $PGM:Pgm </k>
endmodule
