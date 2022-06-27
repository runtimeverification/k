// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-1-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(_S1 SetItem(X:Int), S2 ) ) => . </k> requires X in S2

endmodule
