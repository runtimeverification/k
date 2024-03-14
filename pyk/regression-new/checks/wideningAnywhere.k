// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module WIDENINGANYWHERE

syntax Foo ::= "foo"
syntax KItem ::= "bar"

rule foo => bar [anywhere]

endmodule
