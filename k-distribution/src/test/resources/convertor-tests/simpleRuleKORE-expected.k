// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9"))]
  syntax Exp [Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"12"))]
  rule #KRewrite(#token(KVariable,"A"),#token(KVariable,"B")) requires null ensures null [Location(#token(Int,"5"),#token(Int,"3"),#token(Int,"5"),#token(Int,"13")) contentStartColumn(#token(Int,"8")) contentStartLine(#token(Int,"5"))]
endmodule