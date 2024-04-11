// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// test error messages

requires "demo.k"

module VERIFICATION
    imports DEMO
endmodule

module RHS-VARS-BROKEN-SPEC
    imports VERIFICATION

   claim <k> .K => _ </k>

   claim <k> .K => A </k>
endmodule
