// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  rule #token("#Bool", "true")() => INJECTED-KLIST(#token("#Bool", "true")()) requires '_andBool_(#token("Bool", "true")(),, #token("Bool", "true")())
  rule #token("#Bool", "true")() => INJECTED-KLIST() requires '_andBool_(#token("Bool", "true")(),, #token("Bool", "true")())
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax Bool ::= #Bool


endmodule

