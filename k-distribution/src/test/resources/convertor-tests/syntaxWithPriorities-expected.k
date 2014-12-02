// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST
  syntax priority 'x > 'y 'z > 't > 'u
  syntax associativity right 'y
  syntax associativity left 'x
  syntax Foo ::= "z"
  syntax Foo ::= "y" [someattribute()]
  syntax Foo ::= "x"
  syntax Foo ::= "u" [off()]
  syntax Foo ::= "t" [andanohter()]
endmodule
