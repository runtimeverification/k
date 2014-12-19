// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"5")),endColumn(#token(Int,"9")))]
  syntax Foo ::= "y" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"25")),endLine(#token(Int,"4")),endColumn(#token(Int,"27")))]
  syntax Foo ::= "x" [location(startLine(#token(Int,"4")),startColumn(#token(Int,"19")),endLine(#token(Int,"4")),endColumn(#token(Int,"21")))]
endmodule
