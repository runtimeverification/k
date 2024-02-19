// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
require "substitution.md"

module BINDER
  imports KVAR

  syntax Error ::= foo() [binder]

  syntax Error ::= foo(Error, Error) [binder]

  syntax Correct ::= foo(KVar, Error) [binder]
endmodule
