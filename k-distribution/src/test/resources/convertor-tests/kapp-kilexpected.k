// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  rule '_,_(#token("#Bool", "true")(), #token("#Bool", "true")()) => '.List{"'_,_"}()
  rule 'notBool(#token("#Bool", "true")()) => #token("#Bool", "false")()
  rule notBool #token("#Bool", "false")()  => #token("#Bool", "true")()
  rule notBool #token("#Bool", "true")()  => #token("#Bool", "false")()
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax Bool ::= "notBool" Bool

  syntax Bool ::= #Bool

  syntax Bools ::= List{Bool,","}


endmodule

