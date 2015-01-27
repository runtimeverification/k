// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"13")),endColumn(#token(Int,"9")))]
  syntax priority 'x > 'y 'z > 't > 'u
  syntax associativity right 'y
  syntax associativity left 'x
  syntax Foo ::= "z" [location(startLine(#token(Int,"6")),startColumn(#token(Int,"18")),endLine(#token(Int,"6")),endColumn(#token(Int,"20")))]
  syntax Foo ::= "y" [location(startLine(#token(Int,"5")),startColumn(#token(Int,"18")),endLine(#token(Int,"5")),endColumn(#token(Int,"40"))) someattribute()]
  syntax Foo ::= "x" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"18")),endLine(#token(Int,"4")),endColumn(#token(Int,"20")))]
  syntax Foo ::= "u" [location(startLine(#token(Int,"8")),startColumn(#token(Int,"18")),endLine(#token(Int,"8")),endColumn(#token(Int,"29"))) off()]
  syntax Foo ::= "t" [andanohter() location(startLine(#token(Int,"7")),startColumn(#token(Int,"18")),endLine(#token(Int,"7")),endColumn(#token(Int,"36")))]
endmodule
