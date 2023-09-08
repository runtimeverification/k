module KORE-RPC-TEST-SYNTAX
    imports INT-SYNTAX
    imports BOOL-SYNTAX
endmodule


module KORE-RPC-TEST
    imports KORE-RPC-TEST-SYNTAX
    imports INT
    imports BOOL

    rule [r01]: 0 => 1
    rule [r12]: 1 => 2
    rule [r23]: 2 => 3
    rule [r24]: 2 => 4
    rule [r34]: 3 => 4 ensures false
    rule [r45]: 4 => 5
    rule [r56]: 5 => 6

endmodule
