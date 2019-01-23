// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/simpleRuleKORE.k",KString))]
  syntax Exp [Location(#token("4",Int),#token("3",Int),#token("4",Int),#token("12",Int)) Source(#token("src/test/resources/convertor-tests/simpleRuleKORE.k",KString))]
  rule #KRewrite(#token("A",KVariable),#token("B",KVariable)) requires null ensures null [Location(#token("5",Int),#token("3",Int),#token("5",Int),#token("13",Int)) Source(#token("src/test/resources/convertor-tests/simpleRuleKORE.k",KString)) contentStartColumn(#token("8",Int)) contentStartLine(#token("5",Int))]
endmodule
