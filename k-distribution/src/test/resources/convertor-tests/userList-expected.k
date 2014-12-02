// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax UserList ::= UserList "," UserList [Stx]
  syntax UserList ::= Stx [Stx]
  syntax UserList ::= ".UserList" [Stx]
  syntax Stx ::= "1"
endmodule
