// check for #1845
module LHSFUNCCAST-SYNTAX

endmodule

module LHSFUNCCAST
    imports INT
    imports BOOL
    imports LHSFUNCCAST-SYNTAX

    configuration <k> $PGM:Int </k>

    syntax Int ::= bool2Word ( Bool ) [function]
 // --------------------------------------------
    rule bool2Word(B):Int => #if B #then 1 #else 0 #fi [macro]
endmodule
