// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module POLY-UNPARSING-SYNTAX
  imports ML-SYNTAX
  imports INT
  imports MAP

  syntax Pgm ::= ".Pgm"
endmodule

module POLY-UNPARSING
  imports POLY-UNPARSING-SYNTAX
  configuration <k color="green"> $PGM:Pgm </k>
endmodule
