// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module TEST [org.kframework.attributes.Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"5"),#token(Int,"9"))]
  syntax Foo ::= "y" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"25"),#token(Int,"4"),#token(Int,"27"))]
  syntax Foo ::= "x" [org.kframework.attributes.Location(#token(Int,"4"),#token(Int,"19"),#token(Int,"4"),#token(Int,"21"))]
endmodule
