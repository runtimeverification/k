// Copyright (c) 2014 K Team. All Rights Reserved.

DEF: null -> null
require "include.k"
module INCLUDE
  syntax Map ::= ".Map"

  syntax String ::= #String

  syntax #Bool ::= "false"

  syntax #String ::= Lexical{"\"" ((~[\"\n\r\\]) | (((([\\][nrtf\"\\]) | ([\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* "\""}

  syntax #Bool ::= "true"


endmodule
module TEST
  imports INCLUDE
  configuration <t> <k> .K </k> <env> .Map  </env> <stack> .Bag </stack>  </t>

endmodule

??? check attributes
