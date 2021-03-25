module CHECKFUNCRULEATT-SYNTAX
endmodule
module CHECKFUNCRULEATT
    imports CHECKFUNCRULEATT-SYNTAX
    imports INT
    syntax FOO ::= "foo" [function]
                 | Int
    configuration <k> foo </k>
                  <notk> 0 </notk>
    rule foo => 0 [macro]
    rule foo => 1 [macro-rec]
    rule foo => 2 [alias]
    rule foo => 3 [alias-rec]
    rule foo => 4
    rule <k> 5 => foo </k>
    rule [[ foo => 6 ]]
         <notk> 7 </notk> [macro]
    rule [[ foo => 8 ]]
         <notk> 9 </notk>
endmodule
