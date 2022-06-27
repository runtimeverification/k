// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-1-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(S1 SetItem(X:Int), S2) ) => done ( intersectSet(S1, S2) ) </k>
    requires notBool X in S2

endmodule
