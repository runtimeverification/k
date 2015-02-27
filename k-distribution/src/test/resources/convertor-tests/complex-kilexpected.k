// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  rule #token("#Bool", "true")() => INJECTED-KLIST(#token("#Bool", "true")())
  rule #token("#Bool", "true")() => INJECTED-KLIST()
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax Bool ::= #Bool


endmodule