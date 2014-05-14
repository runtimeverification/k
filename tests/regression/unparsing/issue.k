// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE

syntax Exp ::= foo(Bool, KLabel, Id, Exps)

syntax KLabel ::= "'()"

syntax Exp ::= "foo"
syntax Exps ::= List{Exp,","}

configuration <k> $PGM:K </k> <in stream="stdin"> .List </in>

endmodule
