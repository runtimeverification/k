module CHECKFUNCRULEATT-SYNTAX
endmodule
module CHECKFUNCRULEATT
    imports CHECKFUNCRULEATT-SYNTAX
    syntax FOO ::= "foo" [function]
                 | "boo"
    configuration <k> foo </k>
                  <notk> boo </notk>
    rule foo => boo [macro]
    rule foo => boo [macro-rec]
    rule foo => boo [alias]
    rule foo => boo [alias-rec]
    rule foo => boo
    rule <k> boo => foo </k>
    rule [[ foo => boo ]]
         <notk> boo </notk> [macro]
    rule [[ foo => boo ]]
         <notk> boo </notk>
endmodule
