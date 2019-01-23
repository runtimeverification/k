// Copyright (c) 2014-2019 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("5",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString))]
  syntax Foo ::= "y" [Location(#token("4",Int),#token("25",Int),#token("4",Int),#token("27",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString)) klabel(#token("y",KString))]
  syntax Foo ::= "x" [Location(#token("4",Int),#token("19",Int),#token("4",Int),#token("21",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithOR.k",KString)) klabel(#token("x",KString))]
endmodule
