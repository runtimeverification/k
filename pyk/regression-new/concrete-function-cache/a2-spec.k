// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module A2-SPEC

imports A

claim [s2]:
<k> begin(bar(X)) => end(baz(X)) </k>
requires X <Int 0

endmodule
