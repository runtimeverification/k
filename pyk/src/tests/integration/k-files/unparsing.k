module UNPARSING
    imports BOOL
    imports INT

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= Bool | Int

    syntax Int ::= "hundred" [klabel(hundred), symbol, alias]
    rule hundred => 100

    syntax Bool ::= rangeHundred ( Int ) [klabel(rangeHundred), symbol, alias]
    rule rangeHundred(X) => 0 <=Int X andBool X <Int hundred

    syntax Int ::= labeled(label1: Int, label2: Int) [function, klabel(labeled), symbol]
                 | someLabeled(label1: Int, Int)     [function, klabel(some-labeled), symbol]
                 | noneLabeled(Int, Int)             [function, klabel(none-labeled), symbol]
                 | nonNonTerms()                     [function, klabel(no-nonterms), symbol]

endmodule
