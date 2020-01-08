module INVALIDSYMBOL

syntax Foo ::= foo() [klabel(#KToken), symbol]

syntax Bar ::= bar() [klabel(foo), symbol]
syntax Baz ::= baz() [klabel(foo), symbol]

syntax Exp ::= Val
syntax Val ::= "val"
syntax Exps ::= List{Exp,","} [klabel(exps)]
syntax Vals ::= List{Val,","} [klabel(exps)]

endmodule
