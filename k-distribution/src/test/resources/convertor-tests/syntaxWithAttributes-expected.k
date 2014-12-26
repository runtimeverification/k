// Copyright (c) 2014 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"5")),endColumn(#token(Int,"9")))]
  syntax Foo [location(startLine(#token(Int,"4")),startColumn(#token(Int,"3")),endLine(#token(Int,"4")),endColumn(#token(Int,"24"))) some(foo)]
endmodule
