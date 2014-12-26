// Copyright (c) 2014 K Team. All Rights Reserved.
Require(include.k)

module INCLUDE [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"12")),endColumn(#token(Int,"9")))]
  syntax String ::= #String [location(startLine(#token(Int,"6")),startColumn(#token(Int,"21")),endLine(#token(Int,"6")),endColumn(#token(Int,"27")))]
  syntax Map ::= ".Map" [function() hook(Map:.Map) location(startLine(#token(Int,"8")),startColumn(#token(Int,"18")),endLine(#token(Int,"8")),endColumn(#token(Int,"74")))]
  syntax #String ::= r"\"\\\"\" ((~[\\\"\\n\\r\\\\]) | (((([\\\\][nrtf\\\"\\\\]) | ([\\\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* \"\\\"\"" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"22")),endLine(#token(Int,"5")),endColumn(#token(Int,"166"))) regex([\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"])]
  syntax #Bool ::= "true" [location(startLine(#token(Int,"10")),startColumn(#token(Int,"20")),endLine(#token(Int,"10")),endColumn(#token(Int,"25")))]
  syntax #Bool ::= "false" [location(startLine(#token(Int,"11")),startColumn(#token(Int,"20")),endLine(#token(Int,"11")),endColumn(#token(Int,"26")))]
endmodule


module TEST [location(startLine(#token(Int,"4")),startColumn(#token(Int,"1")),endLine(#token(Int,"7")),endColumn(#token(Int,"9")))]
  imports INCLUDE [location(startLine(#token(Int,"5")),startColumn(#token(Int,"3")),endLine(#token(Int,"5")),endColumn(#token(Int,"17")))]
  configuration <t>KBag(k(.K) [cell()],env('.Map() [location(startLine(#token(Int,"6")),startColumn(#token(Int,"70")),endLine(#token(Int,"6")),endColumn(#token(Int,"74"))) sort(Map)]) [cell()],stack(KBag()) [cell()])</t> ensures #token(KBoolean,"true")
endmodule
