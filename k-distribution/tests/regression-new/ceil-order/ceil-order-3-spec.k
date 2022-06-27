// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-3-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(S SetItem(X:Int), SetItem(Y:Int) ) ) => done ( intersectSet(S, SetItem(Y:Int) ) ) </k>
    requires X =/=K Y

endmodule
