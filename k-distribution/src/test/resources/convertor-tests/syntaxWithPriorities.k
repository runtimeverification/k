// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST
  syntax Foo ::= "x"
               | "y"     [someattribute]
               | "z"
               | "t"    [andanohter]
               | "u"    [off]

  syntax priority x > y z > t > u
  syntax left x
  syntax right y
endmodule
