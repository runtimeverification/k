// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("5",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString))]
  syntax Foo ::= "y" [#klabel(#token("y",KString)) Location(#token("4",Int),#token("25",Int),#token("4",Int),#token("27",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString))]
  syntax Foo ::= "x" [#klabel(#token("x",KString)) Location(#token("4",Int),#token("19",Int),#token("4",Int),#token("21",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString))]
endmodule
