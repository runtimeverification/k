// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token("3",Int),#token("1",Int),#token("6",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString))]
  syntax Stxs ::= Stx "," Stxs [Location(#token("5",Int),#token("21",Int),#token("5",Int),#token("42",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) foo(#token("",AttributeValue)) klabel(#token("_,_",KString)) right() userList(#token("*",KString))]
  syntax Stxs ::= ".Stxs" [Location(#token("5",Int),#token("21",Int),#token("5",Int),#token("42",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) foo(#token("",AttributeValue)) klabel(#token(".List{\"'_,_\"}",KString)) userList(#token("*",KString))]
  syntax Stx ::= "1" [Location(#token("4",Int),#token("20",Int),#token("4",Int),#token("22",Int)) Source(#token("src/test/resources/convertor-tests/userList.k",KString)) klabel(#token("1",KString))]
endmodule
