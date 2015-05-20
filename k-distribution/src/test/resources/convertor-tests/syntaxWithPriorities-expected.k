// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("13",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString))]
  syntax priority x > y z > t > u
  syntax associativity right y
  syntax associativity left x
  syntax Foo ::= "z" [#klabel(#token("z",KString)) Location(#token("6",Int),#token("18",Int),#token("6",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString))]
  syntax Foo ::= "y" [#klabel(#token("y",KString)) Location(#token("5",Int),#token("18",Int),#token("5",Int),#token("40",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString)) someattribute(#token("",AttributeValue))]
  syntax Foo ::= "x" [#klabel(#token("x",KString)) Location(#token("4",Int),#token("18",Int),#token("4",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString))]
  syntax Foo ::= "u" [#klabel(#token("u",KString)) Location(#token("8",Int),#token("18",Int),#token("8",Int),#token("29",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString)) off(#token("",AttributeValue))]
  syntax Foo ::= "t" [#klabel(#token("t",KString)) Location(#token("7",Int),#token("18",Int),#token("7",Int),#token("36",Int)) Source(#token("src/test/resources/convertor-tests/syntaxWithPriorities.k",KString)) andanohter(#token("",AttributeValue))]
endmodule
