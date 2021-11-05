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
  syntax Int ::= A ( Int ) [macro]
  rule A ( N ) => N +Int 1
  rule A ( N ) => N [simplification]
endmodule
