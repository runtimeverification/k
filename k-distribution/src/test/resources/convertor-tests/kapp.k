// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  syntax Bool ::= #Bool

  syntax Bool ::= "notBool" Bool

  rule notBool true => false
  rule notBool false => true
endmodule
