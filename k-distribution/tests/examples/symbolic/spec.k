// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module SPEC

imports A

// TODO: indeed, this rule shouldn't be proved due to the partial rules
rule <k> if(symIExp(N:Int)) => ?I:Int ... </k>
     ensures (?I ==K 0 andBool iexp(N) ==K 0)
      orBool (?I ==K 1 andBool iexp(N) ==K 1)

endmodule
