// Copyright (c) 2019 K Team. All Rights Reserved.

module CRASH-SPEC
    imports VERIF

    claim <k> doIt(foo) => doIt(0) ... </k>
    claim <k> crash(foo) => doIt(0) ... </k>

endmodule
