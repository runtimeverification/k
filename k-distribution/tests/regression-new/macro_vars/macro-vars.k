// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module MACRO-VARS-SYNTAX
endmodule
module MACRO-VARS
  imports MACRO-VARS-SYNTAX
  imports DOMAINS
  syntax KResult ::= Int | Bool
  syntax CPPType ::= bar(Set, CPPSimpleType)
  syntax CPPSimpleType ::= scopedEnum() | unscopedEnum()
  syntax Foo ::= foo(CPPType)
  syntax K ::= inverseConvertType(CPPType, Foo) [function]
  rule inverseConvertType(cppEnumType, foo((cppEnumType #as T::CPPType => underlyingType(T))))
  syntax CPPType ::= underlyingType(CPPType) [function]
  syntax CPPType ::= "cppEnumType" [macro]
  rule cppEnumType => bar(_, scopedEnum() #Or unscopedEnum() ) [unboundVariables(_)]

  syntax Int ::= "hookedMacro" [macro]
  rule hookedMacro => 5

endmodule
