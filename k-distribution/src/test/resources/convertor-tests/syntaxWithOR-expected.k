// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"5"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithOR.k"))]
  syntax Foo ::= "y" [Location(#token(Int,"4"),#token(Int,"25"),#token(Int,"4"),#token(Int,"27")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithOR.k")) klabel(#token(KString,"y"))]
  syntax Foo ::= "x" [Location(#token(Int,"4"),#token(Int,"19"),#token(Int,"4"),#token(Int,"21")) Source(#token(KString,"src/test/resources/convertor-tests/syntaxWithOR.k")) klabel(#token(KString,"x"))]
endmodule
