requires "extended.k"

module VERIFICATION-DEMO
    imports DEMO
endmodule

module VERIFICATION-EXTENDED
    imports EXTENDED
    imports VERIFICATION-DEMO
endmodule

module EXTENDED-BAD-MODULE-SPEC
    imports VERIFICATION-EXTENDED

    rule <k> .K => ?_ </k>
endmodule
