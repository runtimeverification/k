// Copyright (c) K Team. All Rights Reserved.
module A1-SPEC

imports A

claim [s1]:
<k> begin(barConcrete(X)) => end(baz(X)) </k>
requires X >Int 0

endmodule
