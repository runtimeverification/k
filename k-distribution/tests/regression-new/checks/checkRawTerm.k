// Copyright (c) K Team. All Rights Reserved.

module CHECKRAWTERM-SYNTAX
  syntax Foo ::= foo() | bar()
endmodule

module CHECKRAWTERM
  imports CHECKRAWTERM-SYNTAX

  rule foo() => #rawTerm(foo())
  rule #rawTerm(foo()) => bar()
endmodule
