require "builtins.k"
require "modules/substitution.k"

module SYMBOLIC-SYNTAX
  // This is a module where productions will be generated at runtime
endmodule

module SYMBOLIC-K
  imports #SMT
  imports BUILTIN-HOOKS
  imports FREE-VARS

  syntax Bool ::= "forall" Set "." Bool [binder, function]
  syntax Bool ::= "exists" Set "." Bool [binder, function]

  /* The following simplification rules assume non-empty sorts. */
  rule forall S:Set . true => true
  rule forall S:Set . false => false
  rule exists S:Set . true => true
  rule exists S:Set . false => false


  syntax String ::= "K2SMTLib" "(" K ")" [klabel(K2SMTLib), function]
  rule K2SMTLib(false) => "false"
  rule K2SMTLib(true)  => "true"
  rule K2SMTLib(I:#Int) => Int2String(I)
  when I >=Int 0
  rule K2SMTLib(I:#Int) => "(- " +String Int2String(absInt(I)) +String ")"
  when I <Int 0

  rule
    K2SMTLib(forall S:Set . B:Bool)
  =>
    "(forall (" +String Vars2SMTLib(S) +String ") "
    +String K2SMTLib(B) +String ")"
  rule
    K2SMTLib(exists S:Set . B:Bool)
  =>
    "(exists (" +String Vars2SMTLib(S) +String ") "
    +String K2SMTLib(B) +String ")"

  syntax String ::= "Vars2SMTLib" "(" Set ")"
  [prefixlabel(Vars2SMTLib), function]
  rule
    Vars2SMTLib(SetItem(V:Variable) S:Set)
  =>
    "(" +String K2SMTLib(V) +String " " +String K2Sort(V) +String ")"
    +String Vars2SMTLib(S)
  rule Vars2SMTLib(.Set) => ""
  
  syntax String ::= "Consts2SMTLib" "(" Set ")"
  [prefixlabel(Consts2SMTLib), function]
  rule
    Consts2SMTLib(SetItem(V:Variable) S:Set)
  =>
    "(declare-fun " +String K2SMTLib(V)
    +String " () " +String K2Sort(V) +String ")\n"
    +String Consts2SMTLib(S)
  rule Consts2SMTLib(.Set) => ""

  syntax String ::= "SMTLibQuery" "(" Bool ")" [klabel(SMTLibQuery), function]
  rule
    SMTLibQuery(B:Bool)
  =>
    "(set-logic AUFNIRA)\n"
    +String Consts2SMTLib(freeVariables(B))
    +String "(assert " +String K2SMTLib(B) +String ")\n"
    +String "(check-sat)\n"

  syntax String ::= "SMTCall" "(" String ")" [function, hook(#SMT:#smtCall_)]
  syntax String ::= "checkSat" "(" Bool ")" [function]
  rule checkSat(B:Bool) => SMTCall(SMTLibQuery(B))


  syntax Bool ::= "isBuiltin" "(" K ")"
  [prefixlabel(isBuiltin), klabel(isBuiltin), predicate]

  syntax Variable ::= "dummy-this-Variable-needed-only-to-declare-sort"
//  syntax Bool ::= "isVariable" "(" K ")"
//  [prefixlabel(isVariable), klabel(isVariable), predicate]

  syntax Bool ::= "isVariable" "(" List ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Set ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Bag ")" [prefixlabel(isVariable), predicate]
  syntax Bool ::= "isVariable" "(" Map ")" [prefixlabel(isVariable), predicate]

  syntax Bool ::= "isKLabelConstant" "(" KLabel ")"
  [prefixlabel(isKLabelConstant), klabel(isKLabelConstant), predicate]


  syntax String ::= "K2Sort" "(" K ")"
  [prefixlabel(K2Sort), klabel(K2Sort), function]

  rule K2Sort(_:#Bool) => "Bool"
  rule K2Sort(_:#Int) => "Int"
  rule K2Sort(_:#Float) => "Float"
  rule K2Sort(_:#String) => "String"
  rule K2Sort(_:#Id) => "Id"


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

  syntax K ::= #getSymLabel(String)  [function]
  rule #getSymLabel(Type:String)
    => String2KLabel("#sym" +String Type)(.List{K})

  syntax K ::= #freshSymSortN(String,Int) [function]
  rule #freshSymSortN(Type:String,I:Int) 
    =>  String2KLabel("#sym" +String Type)(#distinctCounter(I))

  syntax K ::= #freshSymSort(String) [function]
  rule #freshSymSort(Type:String) => #freshSymSortN(Type,0) 

  syntax K ::= #freshSymN(K,Int) [function]
  rule #freshSymN(K:K,I:Int) => #freshSymSortN(K2Sort(K),I)

  syntax K ::= #freshSym(K) [function]
  rule #freshSym(K:K) => #freshSymSortN(K2Sort(K),0)

  // arrays
//  rule K2SMTLib(
endmodule

