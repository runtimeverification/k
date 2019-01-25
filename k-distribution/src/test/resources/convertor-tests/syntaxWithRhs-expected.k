// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString))]
  syntax Foo ::= "1" [Location(#token("4",Int),#token("18",Int),#token("4",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString)) klabel(#token("1",KString))]
  syntax Bar ::= "2" [Location(#token("5",Int),#token("18",Int),#token("5",Int),#token("32",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString)) klabel(#token("2",KString)) some(#token("foo",AttributeValue))]
endmodule
