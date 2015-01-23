// Copyright (c) 2014-2015 K Team. All Rights Reserved.
Require(include.k)

module INCLUDE [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"12")),endColumn(#token(Int,"9")))]
  syntax String ::= #String [location(startLine(#token(Int,"6")),startColumn(#token(Int,"21")),endLine(#token(Int,"6")),endColumn(#token(Int,"27")))]
  syntax Map ::= ".Map" [function() hook(Map:.Map) location(startLine(#token(Int,"8")),startColumn(#token(Int,"18")),endLine(#token(Int,"8")),endColumn(#token(Int,"74")))]
  syntax #String ::= r"\"\\\"\" ((~[\\\"\\n\\r\\\\]) | (((([\\\\][nrtf\\\"\\\\]) | ([\\\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* \"\\\"\"" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"22")),endLine(#token(Int,"5")),endColumn(#token(Int,"166"))) regex([\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"])]
  syntax #Bool ::= "true" [location(startLine(#token(Int,"10")),startColumn(#token(Int,"20")),endLine(#token(Int,"10")),endColumn(#token(Int,"25")))]
  syntax #Bool ::= "false" [location(startLine(#token(Int,"11")),startColumn(#token(Int,"20")),endLine(#token(Int,"11")),endColumn(#token(Int,"26")))]
endmodule


module TEST [location(startLine(#token(Int,"5")),startColumn(#token(Int,"1")),endLine(#token(Int,"13")),endColumn(#token(Int,"9")))]
  syntax Exp ::= Exp "+" Exp [location(startLine(#token(Int,"8")),startColumn(#token(Int,"18")),endLine(#token(Int,"8")),endColumn(#token(Int,"28")))]
  imports INCLUDE [location(startLine(#token(Int,"6")),startColumn(#token(Int,"3")),endLine(#token(Int,"6")),endColumn(#token(Int,"17")))]
  context '_+_(_ [location(startLine(#token(Int,"12")),startColumn(#token(Int,"11")),endLine(#token(Int,"12")),endColumn(#token(Int,"12"))) sort(K)],HOLE(#token(KItem,"")) [location(startLine(#token(Int,"12")),startColumn(#token(Int,"15")),endLine(#token(Int,"12")),endColumn(#token(Int,"19"))) sort(KItem)]) [location(startLine(#token(Int,"12")),startColumn(#token(Int,"11")),endLine(#token(Int,"12")),endColumn(#token(Int,"19"))) sort(Exp)] requires #token(KBoolean,"true")
  context '_+_(HOLE(#token(KItem,"")) [location(startLine(#token(Int,"10")),startColumn(#token(Int,"11")),endLine(#token(Int,"10")),endColumn(#token(Int,"15"))) sort(KItem)],_ [location(startLine(#token(Int,"10")),startColumn(#token(Int,"18")),endLine(#token(Int,"10")),endColumn(#token(Int,"19"))) sort(K)]) [location(startLine(#token(Int,"10")),startColumn(#token(Int,"11")),endLine(#token(Int,"10")),endColumn(#token(Int,"19"))) sort(Exp)] requires #token(KBoolean,"true")
endmodule
