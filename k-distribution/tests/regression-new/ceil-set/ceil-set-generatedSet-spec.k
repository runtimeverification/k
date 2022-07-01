// Copyright (c) 2022 K Team. All Rights Reserved.

requires "ceil-set.k"

module CEIL-SET-GENERATEDSET-SPEC
    imports CEIL-SET

    claim <k> testGenerated(_I1, _I2, _I3, _I4) => . </k>
          <genSet> _GENSET => ?_ </genSet>

endmodule
