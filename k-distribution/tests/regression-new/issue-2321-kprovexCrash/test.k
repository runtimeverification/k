module TEST
    imports BOOL
    imports INT

    syntax Exp ::= Int | Bool
                 | pair(Int, Int) [klabel(pair), symbol]

    syntax KItem ::= "#assume" Exp [klabel(assume), symbol]
    rule #assume true => .K
    rule #assume false => #Bottom

    syntax KItem ::= "#assert" Exp  [klabel(assert), symbol]
                   | "#fail"
    rule #assert true => .K
    rule #assert false => #fail

// Uninterpreted functions
    syntax Int ::= i(Int, Int)   [function, functional, no-evaluators, smtlib(fi), klabel(i)]
endmodule
