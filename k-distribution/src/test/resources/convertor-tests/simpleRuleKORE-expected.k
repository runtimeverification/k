// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [location(startLine(#token(Int,"3")),startColumn(#token(Int,"1")),endLine(#token(Int,"6")),endColumn(#token(Int,"9")))]
  syntax Exp [location(startLine(#token(Int,"4")),startColumn(#token(Int,"3")),endLine(#token(Int,"4")),endColumn(#token(Int,"12")))]
  rule #KRewrite(#token(KVariable,"A") [location(startLine(#token(Int,"1")),startColumn(#token(Int,"1")),endLine(#token(Int,"1")),endColumn(#token(Int,"2")))],#token(KVariable,"B") [location(startLine(#token(Int,"1")),startColumn(#token(Int,"6")),endLine(#token(Int,"1")),endColumn(#token(Int,"7")))]) [location(startLine(#token(Int,"1")),startColumn(#token(Int,"1")),endLine(#token(Int,"1")),endColumn(#token(Int,"7")))] requires null ensures null [location(startLine(#token(Int,"5")),startColumn(#token(Int,"3")),endLine(#token(Int,"5")),endColumn(#token(Int,"13")))]
endmodule
