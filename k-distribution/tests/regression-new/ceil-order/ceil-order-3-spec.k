// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-3-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(S1 SetItem(X:Int), SetItem(X) ) ) => done( SetItem(X) intersectSet(S1, SetItem(X)) ) </k>

endmodule
