// Copyright (c) 2019 K Team. All Rights Reserved.

module JSON-IN
  imports INT
  imports ML-SYNTAX
  configuration <k> $PGM:Pgm </k>
    syntax Pgm ::= init ( Int ) [macro]
  rule init(0) => { 3 #Equals 4 }
  rule init(1) => { 3 #Equals 3 }
endmodule
