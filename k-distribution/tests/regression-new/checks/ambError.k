// issue #1593
// testing that priority between left guarded and
// right guarded operators are properly disambiguated

module AMBERROR-SYNTAX
    imports INT-SYNTAX

    syntax Exp ::= Int

    syntax Exp ::= Exp "+" Exp [klabel(plus), symbol]
                 > "l" Exp     [klabel(lguard), symbol]
                 | Exp "r"     [klabel(rguard), symbol]
endmodule

module AMBERROR
  imports AMBERROR-SYNTAX
    rule . => 1 + l 2 // non ambiguous, should parse
    rule . => 1 r + 2 // non ambiguous, should parse
    rule . => l 1 r   // ambiguous - error
endmodule
