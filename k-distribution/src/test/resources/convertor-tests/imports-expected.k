// Copyright (c) 2014-2015 K Team. All Rights Reserved.
module ANOTHER [Location(#token(Int,"3"),#token(Int,"1"),#token(Int,"4"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/imports.k"))]
endmodule


module TEST [Location(#token(Int,"6"),#token(Int,"1"),#token(Int,"8"),#token(Int,"9")) Source(#token(KString,"src/test/resources/convertor-tests/imports.k"))]
  imports ANOTHER
endmodule
