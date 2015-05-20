// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/userListNonEmpty.k"))]
  syntax Stxs ::= Stxs "," Stxs [Location(#token(Int,"5"),#token(Int,"19"),#token(Int,"5"),#token(Int,"33")) Source(#token(KString,"src/test/resources/convertor-tests/userListNonEmpty.k")) klabel(#token(KString,"_,_")) userList(#token(KString,"Stxs"))]
  syntax Stxs ::= Stx [Location(#token(Int,"5"),#token(Int,"19"),#token(Int,"5"),#token(Int,"33")) Source(#token(KString,"src/test/resources/convertor-tests/userListNonEmpty.k")) userList(#token(KString,"Stxs"))]
  syntax Stx ::= "1" [Location(#token(Int,"4"),#token(Int,"18"),#token(Int,"4"),#token(Int,"20")) Source(#token(KString,"src/test/resources/convertor-tests/userListNonEmpty.k")) klabel(#token(KString,"1"))]
endmodule
