// Copyright (c) 2016-2019 K Team. All Rights Reserved.
module ANOTHER [org.kframework.attributes.Location(Location(3,1,4,9)) org.kframework.attributes.Source(Source(src/test/resources/convertor-tests/imports.k))]
endmodule


module TEST [org.kframework.attributes.Location(Location(6,1,8,9)) org.kframework.attributes.Source(Source(src/test/resources/convertor-tests/imports.k))]
  imports ANOTHER
endmodule
