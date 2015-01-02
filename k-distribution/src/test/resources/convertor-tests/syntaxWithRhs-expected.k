// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(6),endColumn(9))]
  syntax Foo ::= "1" [location(startLine(4),startColumn(18),endLine(4),endColumn(20))]
  syntax Bar ::= "2" [location(startLine(5),startColumn(18),endLine(5),endColumn(32)) some(foo)]
endmodule
