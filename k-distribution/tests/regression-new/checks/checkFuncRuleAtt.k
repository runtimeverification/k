module CHECKFUNCRULEATT-SYNTAX
endmodule
module CHECKFUNCRULEATT
    imports CHECKFUNCRULEATT-SYNTAX
    syntax FOO ::= "foo" [function]
                 | "boo"
    rule foo => boo [macro]
    rule foo => boo [macro-rec]
    rule foo => boo [alias]
    rule foo => boo [alias-rec]
endmodule
