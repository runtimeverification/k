// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("12",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString))]
  syntax priority x > y z > t m > u
  syntax associativity right u
  syntax associativity left t m
  syntax Foo ::= "z" [Location(#token("6",Int),#token("18",Int),#token("6",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) klabel(#token("z",KString))]
  syntax Foo ::= "y" [Location(#token("5",Int),#token("18",Int),#token("5",Int),#token("40",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) klabel(#token("y",KString)) someattribute(#token("",AttributeValue))]
  syntax Foo ::= "x" [Location(#token("4",Int),#token("18",Int),#token("4",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) klabel(#token("x",KString))]
  syntax Foo ::= "u" [Location(#token("11",Int),#token("18",Int),#token("11",Int),#token("29",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) klabel(#token("u",KString)) off(#token("",AttributeValue))]
  syntax Foo ::= "t" [Location(#token("8",Int),#token("18",Int),#token("8",Int),#token("36",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) andanohter(#token("",AttributeValue)) klabel(#token("t",KString))]
  syntax Foo ::= "m" [Location(#token("9",Int),#token("18",Int),#token("9",Int),#token("20",Int)) Source(#token("src/test/resources/convertor-tests/syntaxPriorities.k",KString)) klabel(#token("m",KString))]
endmodule
