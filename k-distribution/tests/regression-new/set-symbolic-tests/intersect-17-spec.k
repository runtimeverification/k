// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module INTERSECT-17-SPEC
    imports SET-TESTS

    claim <k> intersect ( intersectSet(S1 SetItem(X:MyId), S2 ) )                 => . </k>

endmodule
