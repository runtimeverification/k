// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module RECORDONRHS
  imports INT

syntax Foo ::= foo(Int)

rule _Gen0 => foo(...)

endmodule
