// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST-FAIL-SPEC
    imports VERIF

    claim <k> doIt(-3) => doIt(0) ... </k>
endmodule
