module TEST-SYNTAX
   imports INT-SYNTAX

   syntax Pgm ::= List{Int, ""}
endmodule

module TEST
  imports TEST-SYNTAX
  imports INT

  configuration <k> $PGM:Pgm </k>

endmodule
