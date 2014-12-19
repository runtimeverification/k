// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"6")),endColumn(#token(Int,"9")))]
  syntax Foo ::= "1" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"18")),endLine(#token(Int,"4")),endColumn(#token(Int,"20")))]
  syntax Bar ::= "2" [location(startLine(#token(Int,"5")),startColumn(#token(Int,"18")),endLine(#token(Int,"5")),endColumn(#token(Int,"32"))) some(foo)]
endmodule
