module FORMAT-SYNTAX
    imports INT-SYNTAX

    syntax Exp ::= Int

    // general production
    syntax Exp ::= Exp "+" Exp

    // general production with format
    syntax Exp ::= Exp "-" Exp [format(%1 - %3)]

    // production with color
    syntax Exp ::= Exp "*" Exp [color(green)]

    // runtimeverification/k#4077 - production with format and regex terminal
    syntax Exp ::= r"#exp" [format(#exp)]

    // production with colors
    syntax Exp ::= "foo" Exp "bar" Exp "baz" [colors(red, green, blue)]

    // prefix production
    syntax Exp ::= add ( Exp , Exp )

    // prefix production with format
    syntax Exp ::= sub ( Exp , Exp )  [format(%3 - %5)]

    // record production
    syntax Exp ::= mul ( x: Exp , y : Exp )

    // record production with format
    syntax Exp ::= div ( x: Exp , y : Exp ) [format(%3 / %5)]
endmodule

module FORMAT
    imports FORMAT-SYNTAX
endmodule
