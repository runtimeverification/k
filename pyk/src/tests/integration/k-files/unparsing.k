module UNPARSING
    imports BOOL
    imports INT

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= Bool | Int

    syntax Int ::= "hundred" [symbol(hundred), alias]
    rule hundred => 100

    syntax Bool ::= rangeHundred ( Int ) [symbol(rangeHundred), alias]
    rule rangeHundred(X) => 0 <=Int X andBool X <Int hundred

    syntax Int ::= labeled(label1: Int, label2: Int) [function, symbol(labeled)]
                 | someLabeled(label1: Int, Int)     [function, symbol(some-labeled)]
                 | noneLabeled(Int, Int)             [function, symbol(none-labeled)]
                 | nonNonTerms()                     [function, symbol(no-nonterms)]

endmodule
