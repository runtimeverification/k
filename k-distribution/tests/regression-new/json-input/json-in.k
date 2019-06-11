// Copyright (c) 2019 K Team. All Rights Reserved.

requires "kast.k"

module JSON-IN-SYNTAX
  imports INT-SYNTAX
  imports ML-SYNTAX

  syntax Pgm ::= init ( Int )
  rule init(0) => { 3 #Equals 4 } [macro]
  rule init(1) => { 3 #Equals 3 } [macro]
endmodule

module JSON-IN
  imports JSON-IN-SYNTAX
  configuration <k color="green"> $PGM:Pgm </k>
endmodule
