// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module DIFF-10-SPEC
    imports SET-TESTS

    claim <k> diff ( SetItem(X)           -Set (S SetItem(X:MyId)) )  => . </k>

endmodule
