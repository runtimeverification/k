// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module UNION-29-SPEC
    imports SET-TESTS

    claim <k> union ( Z:MyId in ( (S SetItem(X:MyId)) |Set SetItem(Y:MyId) ) )     => . </k> requires Y =/=K X andBool Z =/=K Y andBool Z  ==K X

endmodule
