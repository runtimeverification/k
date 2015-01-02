// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(12),endColumn(9))]
  syntax priority 'x > 'y 'z > 'm 't > 'u
  syntax associativity right 'u
  syntax associativity left 'm 't
  syntax Foo ::= "z" [location(startLine(6),startColumn(18),endLine(6),endColumn(20))]
  syntax Foo ::= "y" [location(startLine(5),startColumn(18),endLine(5),endColumn(40)) someattribute()]
  syntax Foo ::= "x" [location(startLine(4),startColumn(18),endLine(4),endColumn(20))]
  syntax Foo ::= "u" [location(startLine(11),startColumn(18),endLine(11),endColumn(29)) off()]
  syntax Foo ::= "t" [andanohter() location(startLine(8),startColumn(18),endLine(8),endColumn(36))]
  syntax Foo ::= "m" [location(startLine(9),startColumn(18),endLine(9),endColumn(20))]
endmodule
