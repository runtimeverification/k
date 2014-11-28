// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module META-K
  syntax Set ::= #variables(K)    [function, hook(#META-K:#variables), impure]
  syntax K ::= #rename(K, Set)    [function, hook(#META-K:#rename), impure]
endmodule
