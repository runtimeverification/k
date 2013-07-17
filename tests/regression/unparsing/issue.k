module ISSUE

syntax Exp ::= foo(Bool, KLabel, Id, Exps)

syntax KLabel ::= "'()"

syntax Exp ::= "foo"
syntax Exps ::= List{Exp,","}

configuration <k> $PGM:K </k> <in stream="stdin"> .List </in>

endmodule
