// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module CLAIM-SPEC
    imports ERRORCLAIM

    syntax Int ::= "noError" [token]
    claim <k> doIt(foo) => doIt(0) ... </k>
endmodule
