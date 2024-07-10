// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module INVALIDSYMBOL

syntax Foo ::= foo() [symbol(#KToken)]

syntax Bar ::= bar() [symbol(foo)]
syntax Baz ::= baz() [symbol(foo)]

syntax Exp ::= Val
syntax Val ::= "val"

endmodule
