// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-4-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(SetItem(X:Int), S SetItem(Y:Int) ) ) => done ( intersectSet(SetItem(X:Int), S ) ) </k>
    requires X =/=K Y

endmodule
