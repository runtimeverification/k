// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

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
