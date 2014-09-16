// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module ISSUE

syntax Foo ::= Bar [klabel('foo)]
syntax Bar ::= "bar"
syntax Baz ::= "baz" Foo

rule X:Baz => .

endmodule
