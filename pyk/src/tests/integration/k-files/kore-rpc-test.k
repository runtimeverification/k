module KORE-RPC-TEST-SYNTAX
    imports INT-SYNTAX
endmodule


module KORE-RPC-TEST
    imports KORE-RPC-TEST-SYNTAX

    rule [r01]: 0 => 1
    rule [r12]: 1 => 2
    rule [r23]: 2 => 3
    rule [r24]: 2 => 4
    rule [r45]: 4 => 5
    rule [r56]: 5 => 6

endmodule
