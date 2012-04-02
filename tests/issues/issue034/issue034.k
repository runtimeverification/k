

module ISSUE034 is 
  syntax KResult ::= Type | Field | Id
  syntax Type ::= structType ( Id , List{KResult} ) 
  syntax Field ::= typedField ( Type , Id ) 

  rule structType(X':Id, (_,, typedField(T:Type, X:Id),,  _)) => true
 
  syntax K ::= test  | Bool
  syntax Id ::= a | b 
  syntax Type ::= bool
  macro test = structType(a,typedField(bool,b))
end module
