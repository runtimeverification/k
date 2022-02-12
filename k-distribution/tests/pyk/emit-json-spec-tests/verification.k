requires "imp.k"

module VERIFICATION-SYNTAX
    syntax Id ::= "$s" [token]
                | "$n" [token]
endmodule

module VERIFICATION
    imports VERIFICATION-SYNTAX
    imports IMP
endmodule

