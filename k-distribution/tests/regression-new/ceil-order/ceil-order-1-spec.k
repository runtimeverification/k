// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-1-SPEC
    imports CEIL-ORDER

  claim <k> step ( intersectSet(SetItem(X) , S SetItem(X:Int) ) ) => . </k>

endmodule
