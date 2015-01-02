// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(10),endColumn(9))]
  syntax Bool ::= #Bool [location(startLine(6),startColumn(19),endLine(6),endColumn(23))]
  syntax #Bool ::= "true" [location(startLine(4),startColumn(20),endLine(4),endColumn(25))]
  syntax #Bool ::= "false" [location(startLine(5),startColumn(20),endLine(5),endColumn(26))]
  rule true=>#klist(KList(true)) requires true ensures true [location(startLine(9),startColumn(3),endLine(9),endColumn(29))]
  rule true=>#klist(.K) requires true ensures true [location(startLine(8),startColumn(3),endLine(8),endColumn(21))]
endmodule
