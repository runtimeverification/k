// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Bool ::= #Bool
  syntax Bool ::= "notBool" Bool
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  rule 'notBool_(true) [sort(Bool)]=>false requires true ensures true []
  rule 'notBool_(false) [sort(Bool)]=>true requires true ensures true []
endmodule