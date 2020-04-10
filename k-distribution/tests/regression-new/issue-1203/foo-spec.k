module VERIFICATION
    import FOO
endmodule

module FOO-SPEC
     import VERIFICATION

     rule <k> foo => 0 ... </k>
endmodule