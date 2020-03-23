module NOIMPORTFLOAT-SYNTAX
  imports DOMAINS-SYNTAX
   syntax Pgm ::= foo(Float) | bar()
endmodule


module NOIMPORTFLOAT
  imports NOIMPORTFLOAT-SYNTAX
  imports DOMAINS

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                </T>

endmodule
