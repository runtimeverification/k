// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString))]
  syntax Stxs ::= Stxs "," Stxs [#klabel(#token("_,_",KString)) Location(#token("5",Int),#token("21",Int),#token("5",Int),#token("42",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) foo(#token("",AttributeValue)) userList(#token("Stxs",KString))]
  syntax Stxs ::= Stx [Location(#token("5",Int),#token("21",Int),#token("5",Int),#token("42",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) foo(#token("",AttributeValue)) userList(#token("Stxs",KString))]
  syntax Stxs ::= ".Stxs" [#klabel(#token(".List{\"'_,_\"}",KString)) Location(#token("5",Int),#token("21",Int),#token("5",Int),#token("42",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) foo(#token("",AttributeValue)) userList(#token("Stxs",KString))]
  syntax Stx ::= "1" [#klabel(#token("1",KString)) Location(#token("4",Int),#token("20",Int),#token("4",Int),#token("22",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString))]
endmodule
