// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-2-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(SetItem(Y) , S SetItem(X:Int) SetItem(Y:Int) ) ) => . </k>

endmodule
