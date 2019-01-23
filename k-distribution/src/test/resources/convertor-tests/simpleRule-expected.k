// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/simpleRule.k",KString))]
  syntax Exp [Location(#token("4",Int),#token("3",Int),#token("4",Int),#token("12",Int)) Source(#token("src/test/resources/convertor-tests/simpleRule.k",KString))]
  rule =>(A,A) requires _andBool_(#token("true",Bool),isExp(A)) ensures #token("true",Bool) [Location(#token("5",Int),#token("3",Int),#token("5",Int),#token("17",Int)) Source(#token("src/test/resources/convertor-tests/simpleRule.k",KString))]
endmodule
