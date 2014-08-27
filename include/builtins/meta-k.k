// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "set.k"

module META-K
  syntax K ::= #variables(K)        [function, hook(#META-K:#variables)]
             | #rename(K, MySet)    [function, hook(#META-K:#rename)]
endmodule
