// Copyright (c) 2014 K Team. All Rights Reserved.

module NOTSOSIMPLESYNTAX
  syntax Foo ::= "x"     
               > "y"   	[someattribute] 
               | "z"
               > left: 
                 "t"    [andanohter]
               > right:
                 "u"    [off]
endmodule
