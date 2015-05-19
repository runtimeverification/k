// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/userList.k"))]
  syntax Stxs ::= Stxs "," Stxs [Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) Source(#token(KString,"src/test/resources/convertor-tests/userList.k")) foo(#token(AttributeValue,"")) userList(#token(KString,"Stxs")) klabel(#token(KString,"_,_"))]
  syntax Stxs ::= Stx [Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) Source(#token(KString,"src/test/resources/convertor-tests/userList.k")) foo(#token(AttributeValue,"")) userList(#token(KString,"Stxs"))]
  syntax Stxs ::= ".Stxs" [Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) Source(#token(KString,"src/test/resources/convertor-tests/userList.k")) foo(#token(AttributeValue,"")) userList(#token(KString,"Stxs")) klabel(#token(KString,".List{\"'_,_\"}"))]
  syntax Stx ::= "1" [Location(#token(Int,"4"),#token(Int,"20"),#token(Int,"4"),#token(Int,"22")) Source(#token(KString,"src/test/resources/convertor-tests/userList.k")) klabel(#token(KString,"1"))]
endmodule
