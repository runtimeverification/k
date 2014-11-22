// Copyright (c) 2014 K Team. All Rights Reserved.

Require(include.k)

module INCLUDE
  syntax String ::= #String
  syntax Map ::= ".Map" [function() hook(Map:.Map)]
  syntax #String ::=  [regex([\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"])]
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
endmodule


module TEST
  syntax Exp ::= Exp "+" Exp
  imports INCLUDE
  Context('_+_(_,Hole()),KBoolean(true,[]),[])
  Context('_+_(Hole(),_),KBoolean(true,[]),[])
endmodule