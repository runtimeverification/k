// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

    claim <k> runLemma(keccak(_)) => doneLemma(0) ... </k>

endmodule
