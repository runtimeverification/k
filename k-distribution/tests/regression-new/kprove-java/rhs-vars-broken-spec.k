requires "demo.k"

module VERIFICATION
    imports DEMO
endmodule

module RHS-VARS-BROKEN-SPEC
    imports VERIFICATION

   claim <k> .K => _ </k>

   claim <k> .K => A </k>
endmodule
