requires "demo.k"

module VERIFICATION
    imports DEMO
endmodule

module RHS-VARS-BROKEN-SPEC
    imports VERIFICATION

    rule <k> .K => _ </k>

    rule <k> .K => A </k>
endmodule
