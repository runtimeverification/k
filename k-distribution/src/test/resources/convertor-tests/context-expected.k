// Copyright (c) 2014 K Team. All Rights Reserved.

Require(include.k)

module INCLUDE
  syntax String ::= #String
  syntax Map ::= ".Map" [function() hook(Map:.Map)]
  syntax #String ::= r"\"\\\"\" ((~[\\\"\\n\\r\\\\]) | (((([\\\\][nrtf\\\"\\\\]) | ([\\\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* \"\\\"\"" [regex([\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"])]
  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
endmodule


module TEST
  syntax Exp ::= Exp "+" Exp
  imports INCLUDE
  context '_+_(_ [sort(K)],HOLE() [sort(KItem)]) [sort(Exp)] requires true
  context '_+_(HOLE() [sort(KItem)],_ [sort(K)]) [sort(Exp)] requires true
endmodule
