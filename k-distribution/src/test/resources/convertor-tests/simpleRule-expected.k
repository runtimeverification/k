// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"6")),endColumn(#token(Int,"9")))]
  syntax Exp [location(startLine(#token(Int,"4")),startColumn(#token(Int,"3")),endLine(#token(Int,"4")),endColumn(#token(Int,"12")))]
  rule A [location(startLine(#token(Int,"5")),startColumn(#token(Int,"8")),endLine(#token(Int,"5")),endColumn(#token(Int,"13"))) sort(Exp)]=>A [location(startLine(#token(Int,"5")),startColumn(#token(Int,"17")),endLine(#token(Int,"5")),endColumn(#token(Int,"18"))) sort(Exp)] requires #token(KBoolean,"true") ensures #token(KBoolean,"true") [location(startLine(#token(Int,"5")),startColumn(#token(Int,"3")),endLine(#token(Int,"5")),endColumn(#token(Int,"17")))]
endmodule
