// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

    claim <k> runLemma(3 +Int 7) => doneLemma(10) ... </k>

endmodule
