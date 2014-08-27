// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "builtins.k"
require "modules/substitution.k"
// require "simplification.k"

module SYMBOLIC-SYNTAX
  // This is a module where productions will be generated at runtime

  syntax "#" -/- [s].[y].[m]
endmodule

module SYMBOLIC-K
  imports #SMT
  imports BUILTIN-HOOKS
  imports ID-HOOKS
  imports FREE-VARS
  imports SYMBOLIC-SYNTAX
//  imports SIMPLIFICATION

  syntax Bool ::= "forall" Set "." Bool [binder]
  syntax Bool ::= "exists" Set "." Bool [binder]
  syntax KLabel ::= "#symEqualitySort"

  /* The following simplification rules assume non-empty sorts. */
  rule forall _:Set . true => true
  rule forall _:Set . false => false
  rule exists _:Set . true => true
  rule exists _:Set . false => false

  /* Translation to SMTLib */
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

//  syntax String ::= "#lib" [function]
//  rule #lib => "(declare-fun gcd (Int Int) Int)\n (define-fun minInt ((x Int) (y Int)) Int (ite (< x y) x y) )\n"
//  syntax Int ::= "min-Int" "(" Int "," Int ")" [function, smtlib(minInt)]

  syntax String ::= "SMTLibQuery" "(" Bool ")" [klabel(SMTLibQuery), function]
  rule
    SMTLibQuery(B:Bool)
  =>
    "(set-logic AUFNIRA)\n"
    +String Consts2SMTLib(freeVariables(B))
//    +String #lib +String "\n"
    +String "(assert " +String K2SMTLib(B) +String ")\n"
    +String "(check-sat)\n"

  syntax String ::= "SMTCall" "(" String ")" [function, hook(#SMT:#smtCall_)]
  syntax String ::= checkSat(Bool) [function]
  rule checkSat(B:Bool) => SMTCall(SMTLibQuery(B))
//  rule checkSat(B:Bool) => SMTCall(SMTLibQuery(unflat(dnf(B))))
  rule checkSat(false) => "unsat"

  syntax Variable
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
  rule K2Sort(_:Id) => "Id"
//  rule K2Sort(_:Array) => "(Array Int Int)" // support only integer arrays

  // declare isSymbolicSort for List, Set, Bag and Map
  syntax KItem ::= "isSymbolicBag" "(" Bag ")" [prefixlabel(isSymbolicBag), predicate]

  syntax KItem ::= isSymbolicK(List)

  // define isSymbolicK
  //rule
    //isSymbolicK(L:List) => isSymbolicList(L)
  //[predicate]
  //rule
    //isSymbolicK(S:Set) => isSymbolicSet(S)
  //[predicate]
  //rule
    //isSymbolicK(B:Bag) => isSymbolicBag(B)
  //[predicate]
  //rule
    //isSymbolicK(M:Map) => isSymbolicMap(M)
  //[predicate]
  rule isSymbolicK(KL:KLabel(LK:KList)) => false
  when isBuiltin(KL(LK))
  rule isSymbolicK(KL:KLabel(LK:KList)) => false
  when isToken(KL(LK))
  rule
    isSymbolicK(KL:KLabel(LK:KList))
  =>
    (isVariable(KL(LK)) ==K true) orElseBool (isSymbolicK(LK) ==K true)
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
    isSymbolicK(K1:K,,K2:K,,LK:KList)
  =>
    isSymbolicK(K1) orElseBool isSymbolicK(K2) orElseBool isSymbolicK(LK)
  [predicate]
  rule isSymbolicK(.KList) => false [predicate]

  syntax K ::= #getSymLabel(String)  [function]
  rule #getSymLabel(Type:String)
    => String2KLabel("#sym" +String Type)(.KList)

  syntax K ::= #freshSymSortN(String,Int) [function]
  rule #freshSymSortN(Type:String,I:Int)
    =>  String2KLabel("#sym" +String Type)(#distinctCounter(I))

  syntax K ::= #freshSymSort(String) [function]
  rule #freshSymSort(Type:String) => #freshSymSortN(Type,0)

  syntax K ::= #freshSymN(K,Int) [function]
  rule #freshSymN(K:K,I:Int) => #freshSymSortN(K2Sort(K),I)

  syntax K ::= #freshSym(K) [function]
  rule #freshSym(K:K) => #freshSymSortN(K2Sort(K),0)

/*  syntax K ::= K "==Symbolic" K
  rule I1:Int ==Symbolic I2:Int => I1 ==Int I2 [structural]
  rule B1:Bool ==Symbolic B2:Bool => B1 ==Bool B2 [structural]
  rule S1:String ==Symbolic S2:String => S1 ==String S2 [structural]
*/
  /* K equality - "hardcoded" */
  rule I1:K =K I2:Int => I1 ==Int I2 [anywhere]
  rule B1:K =K B2:Bool => B1 ==Bool B2 [anywhere]
  rule S1:K =K S2:String => S1 ==String S2 [anywhere]
  rule I1:Int =K I2:K => I1 ==Int I2 [anywhere]
  rule B1:Bool =K B2:K => B1 ==Bool B2 [anywhere]
  rule S1:String =K S2:K => S1 ==String S2 [anywhere]

  /* These are needed to print symbolic values */
  rule Int2String(I:Int +Int I':Int) => Int2String(I) +String " +Int " +String Int2String(I')
       when isSymbolicInt(I) orBool isSymbolicInt(I') [anywhere]
  rule Int2String(I:Int *Int I':Int) => Int2String(I) +String " *Int " +String Int2String(I')
       when isSymbolicInt(I) orBool isSymbolicInt(I') [anywhere]
  rule Int2String(I:Int -Int I':Int) => Int2String(I) +String " -Int " +String Int2String(I')
       when isSymbolicInt(I) orBool isSymbolicInt(I') [anywhere]
  rule Int2String(I:Int /Int I':Int) => Int2String(I) +String " /Int " +String Int2String(I')
       when isSymbolicInt(I) orBool isSymbolicInt(I') [anywhere]

  rule Int2String(#symInt(I:Int)) => "#symInt(" +String Int2String(I) +String ")" [anywhere]
  rule Int2String(#symInt(I:Id )) => "#symInt(" +String Id2String(I)  +String ")" [anywhere]

endmodule

