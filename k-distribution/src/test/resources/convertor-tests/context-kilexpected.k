// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module INCLUDE
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax #String ::= Lexical{"\"" ((~[\"\n\r\\]) | (((([\\][nrtf\"\\]) | ([\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* "\""}

  syntax Map ::= ".Map"

  syntax String ::= #String


endmodule
module TEST
  context []:KItem  + _:K
  context _:K + []:KItem
  imports INCLUDE
  syntax Exp ::= Exp "+" Exp


endmodule
require "include.k"

