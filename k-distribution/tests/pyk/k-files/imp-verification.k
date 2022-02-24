requires "imp.k"

module IMP-VERIFICATION-SYNTAX
    syntax Id ::= "$s" [token]
                | "$n" [token]
endmodule

module IMP-VERIFICATION
    imports IMP-VERIFICATION-SYNTAX
    imports IMP
endmodule

