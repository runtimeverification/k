// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "set-tests.k"

module INTERSECT-26-SPEC
    imports SET-TESTS

    claim <k> intersect ( Z:MyId in intersectSet( S SetItem(X:MyId), SetItem(Y:MyId) ) )     => . </k> requires Y =/=K X andBool                  Z  ==K X

endmodule
