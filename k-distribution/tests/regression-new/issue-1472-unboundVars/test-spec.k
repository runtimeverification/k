// Copyright (c) 2020 K Team. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

    claim <k> inc(3) => I </k>
      requires I ==Int 4
endmodule
