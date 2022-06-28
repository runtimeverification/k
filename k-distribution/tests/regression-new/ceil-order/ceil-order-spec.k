// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-order.k"

module CEIL-ORDER-SPEC
    imports CEIL-ORDER

  claim <k> step( (S SetItem(X:Int)) -Set SetItem(X) ) => done(S) </k>
endmodule
