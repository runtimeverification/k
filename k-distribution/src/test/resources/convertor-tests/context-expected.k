// Copyright (c) 2014-2015 K Team. All Rights Reserved.
Require(include.k)

module INCLUDE [location(startLine(3),startColumn(1),endLine(12),endColumn(9))]
  syntax String ::= #String [location(startLine(6),startColumn(21),endLine(6),endColumn(27))]
  syntax Map ::= ".Map" [function() hook(Map:.Map) location(startLine(8),startColumn(18),endLine(8),endColumn(74))]
  syntax #String ::= r"\"\\\"\" ((~[\\\"\\n\\r\\\\]) | (((([\\\\][nrtf\\\"\\\\]) | ([\\\\][x][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][u][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])) | ([\\\\][U][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])))* \"\\\"\"" [location(startLine(4),startColumn(22),endLine(5),endColumn(166)) regex([\"](([^\"\n\r\\])|([\\][nrtf\"\\])|([\\][x][0-9a-fA-F]{2})|([\\][u][0-9a-fA-F]{4})|([\\][U][0-9a-fA-F]{8}))*[\"])]
  syntax #Bool ::= "true" [location(startLine(10),startColumn(20),endLine(10),endColumn(25))]
  syntax #Bool ::= "false" [location(startLine(11),startColumn(20),endLine(11),endColumn(26))]
endmodule


module TEST [location(startLine(5),startColumn(1),endLine(13),endColumn(9))]
  syntax Exp ::= Exp "+" Exp [location(startLine(8),startColumn(18),endLine(8),endColumn(28))]
  imports INCLUDE [location(startLine(6),startColumn(3),endLine(6),endColumn(17))]
  context '_+_(_ [location(startLine(12),startColumn(11),endLine(12),endColumn(12)) sort(K)],HOLE() [location(startLine(12),startColumn(15),endLine(12),endColumn(19)) sort(KItem)]) [location(startLine(12),startColumn(11),endLine(12),endColumn(19)) sort(Exp)] requires true
  context '_+_(HOLE() [location(startLine(10),startColumn(11),endLine(10),endColumn(15)) sort(KItem)],_ [location(startLine(10),startColumn(18),endLine(10),endColumn(19)) sort(K)]) [location(startLine(10),startColumn(11),endLine(10),endColumn(19)) sort(Exp)] requires true
endmodule
