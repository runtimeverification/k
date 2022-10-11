// Copyright (c) 2019 K Team. All Rights Reserved.

module JSON-IN-SYNTAX
  imports INT
  imports ML-SYNTAX

  syntax Pgm ::= init ( Int ) [macro]
  rule init(0) => { 3 #Equals 4 }
  rule init(1) => { 3 #Equals 3 }
  configuration <k> $PGM:Pgm </k>
endmodule

module JSON-IN
  imports JSON-IN-SYNTAX
endmodule
