// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString))]
  syntax Foo ::= "1" [#klabel(#token("1",KString)) Location(#token("4",Int),#token("18",Int),#token("4",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString))]
  syntax Bar ::= "2" [#klabel(#token("2",KString)) Location(#token("5",Int),#token("18",Int),#token("5",Int),#token("32",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithRhs.k",KString)) some(#token("foo",AttributeValue))]
endmodule
