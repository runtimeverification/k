// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9"))]
  syntax Stxs ::= Stxs "," Stxs [#klabel(#token(KString,"'_,_")) foo(#token(AttributeValue,"")) org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) userList(#token(KString,"Stxs"))]
  syntax Stxs ::= Stx [foo(#token(AttributeValue,"")) org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) userList(#token(KString,"Stxs"))]
  syntax Stxs ::= ".Stxs" [#klabel(#token(KString,"'.List{\"'_,_\"}")) foo(#token(AttributeValue,"")) org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"21"),#token(Int,"5"),#token(Int,"42")) userList(#token(KString,"Stxs"))]
  syntax Stx ::= "1" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"20"),#token(Int,"4"),#token(Int,"22"))]
endmodule
