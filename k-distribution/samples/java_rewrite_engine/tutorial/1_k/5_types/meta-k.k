// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module META-K
  syntax Set ::= #variables(KItem)        [function, hook(#META-K:#variables), impure]
  syntax KItem ::= #rename(KItem, Set)    [function, hook(#META-K:#rename), impure]
endmodule

