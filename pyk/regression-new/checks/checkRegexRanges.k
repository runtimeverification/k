// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKREGEXRANGES
syntax lexical Foo = r"a|[1-#]b"
syntax Bar ::= r"a|[1-#]b"

syntax lexical Baz = r"(a|b|c){100,1}"
syntax Buz ::= r"(a|b|c){100,1}"
endmodule
