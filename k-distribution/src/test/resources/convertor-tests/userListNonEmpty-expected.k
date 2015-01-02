// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(3),startColumn(1),endLine(6),endColumn(9))]
  syntax Stxs ::= Stxs "," Stxs [userList(Stxs)]
  syntax Stxs ::= Stx [userList(Stxs)]
  syntax Stx ::= "1" [location(startLine(4),startColumn(18),endLine(4),endColumn(20))]
endmodule
