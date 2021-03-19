module CHECKFUNCRULEATT-SYNTAX
endmodule
module CHECKFUNCRULEATT
    imports CHECKFUNCRULEATT-SYNTAX
    syntax FOO ::= "foo" [function]
                 | "boo"
    rule foo => boo [macro]
endmodule
