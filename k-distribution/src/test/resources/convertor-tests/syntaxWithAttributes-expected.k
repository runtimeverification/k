// Copyright (c) 2014-2016 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("5",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithAttributes.k",KString))]
  syntax Foo [Location(#token("4",Int),#token("3",Int),#token("4",Int),#token("24",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithAttributes.k",KString)) some(#token("foo",AttributeValue))]
endmodule
