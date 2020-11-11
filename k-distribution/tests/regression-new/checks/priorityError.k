// Issue #1593
// priority between left guarded and right guarded
// operators are not properly disambiguated
// so at least give a better error message

module PRIORITYERROR-SYNTAX

endmodule

module PRIORITYERROR
  imports PRIORITYERROR-SYNTAX
    imports INT

    syntax Exp ::= Int

    syntax Exp ::= Exp "+" Exp [klabel(plus), symbol]
                 > "l" Exp     [klabel(lguard), symbol]
                 | Exp "r"     [klabel(rguard), symbol]
    rule . => 1 + l 2 // unable to disambiguate - error
    rule . => 1 r + 2 // unable to disambiguate - error
    rule . => l 1 r   // ambiguous - error
endmodule
