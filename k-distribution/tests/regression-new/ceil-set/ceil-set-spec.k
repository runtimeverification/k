// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-set.k"

module CEIL-SET-SPEC
    imports CEIL-SET

    claim <k> eval ( S1:Set S2:Set ) => . </k>
      requires intersectSet(S1, S2) ==K .Set

endmodule
