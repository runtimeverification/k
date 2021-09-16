require "substitution.md"

module BINDER
  imports KVAR

  syntax Error ::= foo() [binder]

  syntax Error ::= foo(KVar, Error) [binder(1 -> 2)]

  syntax Error ::= foo(Error, Error) [binder]

  syntax Correct ::= foo(KVar, Error) [binder]
endmodule
