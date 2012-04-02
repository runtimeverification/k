

module ISSUE046 imports K
 syntax K ::= a | b | c
 syntax K ::= l ( KLabel )
 syntax Set ::= types
 macro types = Set(l('arrayType),,l('bitfieldType),, l('functionType),, l('pointerType),, l('structType),, l('unionType),, l('qualifiedType))
end module
