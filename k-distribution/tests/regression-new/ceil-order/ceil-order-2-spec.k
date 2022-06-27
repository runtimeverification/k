// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-2-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(S1, S2 SetItem(X:Int)) ) => . </k> requires X in S1

endmodule
