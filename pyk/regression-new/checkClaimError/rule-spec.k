// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module RULE-SPEC
    imports ERRORCLAIM

    rule <k> doIt(foo) => doIt(0) ... </k>
endmodule
