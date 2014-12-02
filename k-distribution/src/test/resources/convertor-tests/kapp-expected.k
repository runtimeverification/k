// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax Bools ::= Bools "," Bools [Bool]
  syntax Bools ::= Bool [Bool]
  syntax Bools ::= ".Bools" [Bool]
  syntax Bool ::= #Bool
  syntax Bool ::= "notBool" Bool
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  rule 'notBool_(true) [sort(Bool)]=>false requires true ensures true []
  rule 'notBool_(false) [sort(Bool)]=>true requires true ensures true []
  rule 'notBool(true)=>false requires true ensures true []
  rule '_,_(true,true) [sort(Bools)]=>'.List{"'_,_"}() [listTerminator()] requires true ensures true []
endmodule
