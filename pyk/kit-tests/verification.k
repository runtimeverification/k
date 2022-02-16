requires "control-flow.k"

module VERIFICATION-SYNTAX
    imports CONTROL-FLOW-SYNTAX

    syntax Id ::= "$s" [token]
                | "$n" [token]
endmodule

module VERIFICATION
    imports VERIFICATION-SYNTAX
    imports CONTROL-FLOW
endmodule

