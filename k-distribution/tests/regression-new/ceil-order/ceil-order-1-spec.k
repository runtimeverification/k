// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-2-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(_S1 SetItem(X:Int), S2 ) ) => done ( SetItem(X:Int) intersectSet(_S1, S2 ) ) </k>
    requires X in S2

endmodule
