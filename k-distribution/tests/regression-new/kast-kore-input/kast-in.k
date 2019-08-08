// Copyright (c) 2019 K Team. All Rights Reserved.

requires "kast.k"

module KAST-IN-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX

  syntax Pgm ::= init ( Int )
  rule init(0) => { 3 #Equals 4 } [macro]
  rule init(1) => { 3 #Equals 3 } [macro]
endmodule

module KAST-IN
  imports KAST-IN-SYNTAX
  configuration <k color="green"> $PGM:Pgm </k>
endmodule
