module INT-LIST
    imports INT-SYNTAX
    syntax Ints ::= List{Int, ","} [symbol(int-list), terminator-symbol(.int-list)]
endmodule
