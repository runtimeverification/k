// Copyright (c) K Team. All Rights Reserved.

module TEST
  syntax Foo ::= "x"
               > "y"     [someattribute]
               | "z"
               > left:
                 "t"    [andanohter]
               | "m"
               > right:
                 "u"    [off]
endmodule
