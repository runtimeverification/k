require "builtins.k"

module SYMBOLIC-K
  imports BUILTIN-HOOKS

  syntax Bool ::= "isBuiltin" "(" K ")"
  [prefixlabel(isBuiltin), klabel(isBuiltin), predicate]

  syntax Bool ::= "isVariable" "(" K ")"
  [prefixlabel(isVariable), klabel(isVariable), predicate]

  syntax Bool ::= "isVariable" "(" List ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Set ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Bag ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Map ")" [prefixlabel(isVariable), predicate]

  syntax Bool ::= "isKLabelConstant" "(" KLabel ")"
  [prefixlabel(isKLabelConstant), klabel(isKLabelConstant), predicate]


  syntax String ::= "K2Sort" "(" K ")"
  [prefixlabel(K2Sort), klabel(K2Sort), function]

  rule K2Sort(_:Bool) => "Bool"
  rule K2Sort(_:Int) => "Int"
  rule K2Sort(_:Float) => "Float"
  rule K2Sort(_:String) => "String"
  rule K2Sort(_:Id) => "Id"


  // declare isSymbolicSort for List, Set, Bag and Map
  syntax K ::= "isSymbolicList" "(" List ")" [prefixlabel(isSymbolicList), predicate]
  syntax K ::= "isSymbolicSet" "(" Set ")" [prefixlabel(isSymbolicSet), predicate]
  syntax K ::= "isSymbolicBag" "(" Bag ")" [prefixlabel(isSymbolicBag), predicate]
  syntax K ::= "isSymbolicMap" "(" Map ")" [prefixlabel(isSymbolicMap), predicate]


  // define isSymbolicK
  rule
    isSymbolicK(List2KLabel(L:List)(.List{K})) => isSymbolicList(L)
  [predicate]
  rule
    isSymbolicK(Set2KLabel(S:Set)(.List{K})) => isSymbolicSet(S)
  [predicate]
  rule
    isSymbolicK(Bag2KLabel(B:Bag)(.List{K})) => isSymbolicBag(B)
  [predicate]
  rule
    isSymbolicK(Map2KLabel(M:Map)(.List{K})) => isSymbolicMap(M)
  [predicate]
  rule isSymbolicK(KL:KLabel(LK:List{K})) => false
  when isBuiltin(KL(LK)) 
  rule
    isSymbolicK(KL:KLabel(LK:List{K}))
  =>
    (isVariable(KL(LK)) ==K true) orElseBool isSymbolicK(LK)
  when isKLabelConstant(KL)
  [predicate]

  rule
    isSymbolicK(K1:K ~> K2:K)
  =>
    isSymbolicK(K1) orElseBool isSymbolicK(K2)
  when K1 =/=K .K andThenBool K2 =/=K .K
  [predicate]
  rule isSymbolicK(.K) => false [predicate]

  rule
    isSymbolicK(K1:K,,K2:K,,LK:List{K})
  =>
    isSymbolicK(K1) orElseBool isSymbolicK(K2) orElseBool isSymbolicK(LK)
  [predicate]
  rule isSymbolicK(.List{K}) => false [predicate]
endmodule

