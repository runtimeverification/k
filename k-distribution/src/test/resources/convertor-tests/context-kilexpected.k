// Copyright (c) 2014 K Team. All Rights Reserved.

DEF: null -> null
require "include.k"
module TEST
  syntax Exp ::= Exp "+" Exp

  imports INCLUDE
  context _:K + []:KItem
  context []:KItem  + _:K

endmodule
module INCLUDE
  syntax String ::= #String

  syntax #String ::= Lexical{"\"" ((~[\"\n\r\\]) | (((([\\][nrtf\"\\]) | ([\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* "\""} [??? attributes]

  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax Map ::= ".Map"


endmodule
