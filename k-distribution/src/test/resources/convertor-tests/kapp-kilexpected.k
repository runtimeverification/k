// Copyright (c) 2014 K Team. All Rights Reserved.

DEF: null -> null
module TEST
  rule notBool #token("#Bool", "false")()  => #token("#Bool", "true")()
  rule notBool #token("#Bool", "true")()  => #token("#Bool", "false")()
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax Bool ::= "notBool" Bool

  syntax Bool ::= #Bool


endmodule
