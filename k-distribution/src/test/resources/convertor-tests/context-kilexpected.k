// Copyright (c) 2014-2019 K Team. All Rights Reserved.
DEF: null -> null
module INCLUDE
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax #String ::= Lexical{[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]}

  syntax Map ::= ".Map"

  syntax String ::= #String


endmodule
module TEST
  context []:KItem  + _:K
  context _:K + []:KItem
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax #String ::= Lexical{[\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"]}

  syntax Exp ::= Exp "+" Exp

  syntax Map ::= ".Map"

  syntax String ::= #String


endmodule

