require "set.k"

module META-K 
  syntax K ::= #variables(K)        [function, hook(#META-K:#variables)]
             | #rename(K, MySet)    [function, hook(#META-K:#rename)]
endmodule
