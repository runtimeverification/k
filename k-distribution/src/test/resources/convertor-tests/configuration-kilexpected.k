// Copyright (c) 2014-2015 K Team. All Rights Reserved.

DEF: null -> null
require "include.k"
module INCLUDE
  syntax #Bool ::= "false"

  syntax #Bool ::= "true"

  syntax #String ::= Lexical{"\"" ((~[\"\n\r\\]) | (((([\\][nrtf\"\\]) | ([\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* "\""}

  syntax Map ::= ".Map"

  syntax String ::= #String


endmodule
module TEST
  configuration <t> <k> .K </k> <env> .Map  </env> <stack> .Bag </stack>  </t>
  imports INCLUDE

endmodule
