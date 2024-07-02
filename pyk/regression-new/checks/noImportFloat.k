// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module NOIMPORTFLOAT-SYNTAX
  imports DOMAINS-SYNTAX
   syntax Pgm ::= foo(x:Float) | bar()
endmodule


module NOIMPORTFLOAT
  imports NOIMPORTFLOAT-SYNTAX
  imports DOMAINS

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                </T>

endmodule
