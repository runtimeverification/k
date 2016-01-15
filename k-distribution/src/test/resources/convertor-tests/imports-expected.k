// Copyright (c) 2014-2016 K Team. All Rights Reserved.
module ANOTHER [Location(#token("3",Int),#token("1",Int),#token("4",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/imports.k",KString))]
endmodule


module TEST [Location(#token("6",Int),#token("1",Int),#token("8",Int),#token("9",Int)) Source(#token("src/test/resources/convertor-tests/imports.k",KString))]
  imports ANOTHER
endmodule
