// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(18),endColumn(9))]
  syntax Bools ::= Bools "," Bools [userList(Bools)]
  syntax Bools ::= Bool [userList(Bools)]
  syntax Bools ::= ".Bools" [userList(Bools)]
  syntax Bool ::= #Bool [location(startLine(6),startColumn(19),endLine(6),endColumn(23))]
  syntax Bool ::= "notBool" Bool [location(startLine(8),startColumn(19),endLine(8),endColumn(32))]
  syntax #Bool ::= "true" [location(startLine(4),startColumn(20),endLine(4),endColumn(25))]
  syntax #Bool ::= "false" [location(startLine(5),startColumn(20),endLine(5),endColumn(26))]
  rule 'notBool_(true) [location(startLine(10),startColumn(8),endLine(10),endColumn(20)) sort(Bool)]=>false requires true ensures true [location(startLine(10),startColumn(3),endLine(10),endColumn(28))]
  rule 'notBool_(false) [location(startLine(11),startColumn(8),endLine(11),endColumn(21)) sort(Bool)]=>true requires true ensures true [location(startLine(11),startColumn(3),endLine(11),endColumn(28))]
  rule 'notBool(true) [location(startLine(13),startColumn(8),endLine(13),endColumn(22))]=>false requires true ensures true [location(startLine(13),startColumn(3),endLine(13),endColumn(30))]
  rule '_,_(true,true) [location(startLine(17),startColumn(8),endLine(17),endColumn(18)) sort(Bools)]=>'.List{"'_,_"}() [listTerminator()] requires true ensures true [location(startLine(17),startColumn(3),endLine(17),endColumn(27))]
endmodule
