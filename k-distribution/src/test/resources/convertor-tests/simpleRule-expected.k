// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9"))]
  syntax Exp [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"12"))]
  rule A=>A requires '_andBool_(#token(Bool,"true"),isExp(A)) ensures #token(Bool,"true") [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"3"),#token(Int,"5"),#token(Int,"17"))]
endmodule
