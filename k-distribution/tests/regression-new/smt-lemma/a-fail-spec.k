// Copyright (c) 2020 K Team. All Rights Reserved.

module A-FAIL-SPEC

imports A

rule <k> zoo(foo(X)) => koo(bar(X)) ... </k>
    requires X <Int 0

endmodule
