// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module INTERSECT-7-SPEC
    imports SET-TESTS

    claim <k> intersect ( intersectSet(S  SetItem(X:MyId), SetItem(Y:MyId) ) )    => . </k> requires Y in S

endmodule
