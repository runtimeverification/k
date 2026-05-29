// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
    imports BOOL
    imports INT

    syntax Exp ::= Int | Bool
                 | pair(Int, Int) [symbol(pair)]

    syntax KItem ::= "#assume" Exp [symbol(assume)]
    rule #assume true => .K
    rule #assume false => #Bottom

    syntax KItem ::= "#assert" Exp  [symbol(assert)]
                   | "#fail"
    rule #assert true => .K
    rule #assert false => #fail

// Uninterpreted functions
    syntax Int ::= i(Int, Int)   [function, total, no-evaluators, smtlib(fi), symbol(i)]
endmodule
