// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/simpleRule.k"))]
  syntax Exp [Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"12")) Source(#token(KString,"src/test/resources/convertor-tests/simpleRule.k"))]
  rule =>(A,A) requires _andBool_(#token(Bool,"true"),isExp(A)) ensures #token(Bool,"true") [Location(#token(Int,"5"),#token(Int,"3"),#token(Int,"5"),#token(Int,"17")) Source(#token(KString,"src/test/resources/convertor-tests/simpleRule.k"))]
endmodule
