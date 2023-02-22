// Copyright (c) K Team. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

    claim <k> runLemma(keccak(_)) => doneLemma(0) ... </k>

endmodule
