// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module INVALIDSYMBOL

syntax Foo ::= foo() [klabel(#KToken), symbol]

syntax Bar ::= bar() [klabel(foo), symbol]
syntax Baz ::= baz() [klabel(foo), symbol]

syntax Exp ::= Val
syntax Val ::= "val"

endmodule
