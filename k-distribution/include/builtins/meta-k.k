// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "set.k"

module META-K
  syntax K ::= #variables(K)        [function, hook(#META-K:#variables), impure]
             | #rename(K, MySet)    [function, hook(#META-K:#rename), impure]
endmodule
