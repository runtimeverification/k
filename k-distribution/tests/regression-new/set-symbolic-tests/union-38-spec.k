// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module UNION-38-SPEC
    imports SET-TESTS

    claim <k> union ( X      in ( (SetItem(X:MyId) SetItem(y)) |Set SetItem(x) ) ) => . </k> requires X =/=K x

endmodule
