// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module UNION-6-SPEC
    imports SET-TESTS

    claim <k> union ( (S  SetItem(X:MyId)) |Set SetItem(Y:MyId) )      => . </k> requires Y =/=K X

endmodule
