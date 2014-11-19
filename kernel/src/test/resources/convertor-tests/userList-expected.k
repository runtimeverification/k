// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax UserList ::= UserList "," UserList []
  syntax UserList ::= Stx []
  syntax UserList ::= ".UserList" []
  syntax Stx ::= "1"
endmodule