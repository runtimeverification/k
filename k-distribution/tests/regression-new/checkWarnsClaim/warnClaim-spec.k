// Copyright (c) K Team. All Rights Reserved.

module WARNCLAIM-SPEC
    imports WARNCLAIM

    rule <k> doIt(foo) => doIt(0) ... </k>
endmodule
