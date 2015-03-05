// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9"))]
  syntax Exp [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"12"))]
  rule #KRewrite(#token(KVariable,"A"),#token(KVariable,"B")) requires null ensures null [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"3"),#token(Int,"5"),#token(Int,"13"))]
endmodule
