// Copyright (c) 2014-2016 K Team. All Rights Reserved.

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
