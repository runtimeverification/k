// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"6"),#token(Int,"9"))]
  syntax Foo ::= "1" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"18"),#token(Int,"4"),#token(Int,"20"))]
  syntax Bar ::= "2" [org.kframework.attributes.Location(#token(Int,"5"),#token(Int,"18"),#token(Int,"5"),#token(Int,"32")) some(#token(AttributeValue,"foo"))]
endmodule
