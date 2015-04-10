// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module TEST [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"5"),#token(Int,"9"))]
  syntax Foo [Location(#token(Int,"4"),#token(Int,"3"),#token(Int,"4"),#token(Int,"24")) some(#token(AttributeValue,"foo"))]
endmodule
