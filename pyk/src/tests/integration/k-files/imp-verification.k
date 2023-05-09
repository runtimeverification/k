requires "imp.k"

module IMP-VERIFICATION-SYNTAX
    syntax Id ::= "$s" [token]
                | "$k" [token]
                | "$m" [token]
                | "$n" [token]
                | "$i" [token]
endmodule

module IMP-VERIFICATION
    imports IMP-VERIFICATION-SYNTAX
    imports IMP

    syntax KItem ::= "#FINISH"

    rule [halt]: <k> #FINISH => . ... </k>
endmodule

