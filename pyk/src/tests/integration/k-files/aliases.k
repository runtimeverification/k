module ALIASES
    imports BOOL
    imports INT

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= Bool | Int

    syntax Int ::= "hundred" [klabel(hundred), symbol, alias]
    rule hundred => 100

    syntax Bool ::= rangeHundred ( Int ) [klabel(rangeHundred), symbol, alias]
    rule rangeHundred(X) => 0 <=Int X andBool X <Int hundred
endmodule
