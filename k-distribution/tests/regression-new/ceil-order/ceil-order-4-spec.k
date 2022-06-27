// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-4-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(S1 SetItem(X:Int), SetItem(Y:Int) ) ) => done ( intersectSet(S1, SetItem(Y:Int) ) ) </k>
    requires X =/=K Y

endmodule
