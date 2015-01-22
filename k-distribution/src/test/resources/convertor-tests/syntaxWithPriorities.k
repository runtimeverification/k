// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST
  syntax Foo ::= "x"
               | "y"     [someattribute]
               | "z"
               | "t"    [andanohter]
               | "u"    [off]

  syntax priorities 'x > 'y 'z > 't > 'u
  syntax left 'x
  syntax right 'y
endmodule
