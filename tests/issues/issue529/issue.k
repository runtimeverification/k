module ISSUE

syntax Fo ::= bar(KLabel)

rule bar(List2KLabel _) => .
rule bar(List{K}2KLabel _) => .

endmodule
