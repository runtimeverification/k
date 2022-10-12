// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-set.k"

module CEIL-SET-CELLSET-SPEC
    imports CEIL-SET

    claim <k> testCell(_I1, _I2, _I3, _I4) => . </k>
          <cellSet> _CELLSET => ?_ </cellSet>

endmodule
