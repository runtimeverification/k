// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "builtins/builtins.k"
require "builtins/fol.k"
require "builtins/array-symbolic.k"

module SMTLIB-CONVERSION
  imports BUILTIN-HOOKS
  imports FOL
  imports ARRAY-SYMBOLIC

  // convert Bool to smtlib
  syntax String ::= "Smtlib" "(" K ")" [function]

  // Smtlib: booleans
  rule Smtlib(false) => "false"
  rule Smtlib(true)  => "true"
  rule Smtlib(symBool(I:Int)) => "var" +String Int2String(I)
  rule Smtlib(symBool(Var:Id)) => Id2String(Var)

  rule Smtlib(B1:Bool ==Bool B2:Bool) => "(= " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")"
  rule Smtlib(B1:Bool =/=Bool B2:Bool) => "(not (= " +String Smtlib(notBool B1) +String  " " +String Smtlib(notBool B2) +String "))"
  rule Smtlib(B1:Bool andBool B2:Bool) => "(and " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")"
  rule Smtlib(B1:Bool orBool B2:Bool) => "(or " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")"
  rule Smtlib(B1:Bool xorBool B2:Bool) => "(xor " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")"
  rule Smtlib(B1:Bool impliesBool B2:Bool) => "(=> " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")"
  rule Smtlib(notBool B:Bool) => "(not " +String Smtlib(B) +String ")"

  // Smtlib: integers
  rule Smtlib(I:#Int) => Int2String(I) when I >=Int 0
  rule Smtlib(I:#Int) => "(- " +String Int2String(0 -Int I) +String ")" when I <Int 0
  rule Smtlib(symInt(I:Int)) => "var" +String Int2String(I)
  rule Smtlib(symInt(Var:Id)) => Id2String(Var)

  rule Smtlib(I1:Int +Int I2:Int) => "(+ " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int *Int I2:Int) => "(* " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int /Int I2:Int) => "(div " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int -Int I2:Int) => "(- " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int %Int I2:Int) => "(% " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"

  rule Smtlib(I1:Int <Int I2:Int) => "(< " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int <=Int I2:Int) => "(<= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int >Int I2:Int) => "(> " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int >=Int I2:Int) => "(>= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int ==Int I2:Int) => "(= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"
  rule Smtlib(I1:Int =/=Int I2:Int) => "(not (= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String "))"

  rule Smtlib(minInt(I1:Int, I2:Int)) => "(minInt " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")"

  rule Smtlib(select A:Array I:Int) => "(select " +String Smtlib(A) +String " " +String Smtlib(I) +String ")"
  rule Smtlib(store A:Array I:Int V:Int) => "(store " +String Smtlib(I) +String " " +String Smtlib(I) +String " " +String Smtlib(V) +String ")"

  // Smtlib: arrays
  rule Smtlib(symArray(X:Id)) => Id2String(X)

  // Smtlib: fol
  rule Smtlib((forall (Is:IntList)(B:Bool))) => "(forall " +String "(" +String Smtlib(Is) +String ")" +String Smtlib(B) +String ")"
  rule Smtlib(notFol F:Fol) => "(not " +String Smtlib(F) +String ")"
  rule Smtlib(F1:Fol orFol  F2:Fol) => "(or "  +String Smtlib(F1) +String " " +String  Smtlib(F2) +String ")"
  rule Smtlib(F1:Fol andFol F2:Fol) => "(and " +String Smtlib(F1) +String " " +String  Smtlib(F2) +String ")"
  rule Smtlib(I:Int ; R:IntList) => "(" +String Smtlib(I) +String " Int) " +String Smtlib(R)
  rule Smtlib(.IntList) => ""

  //@ Collecting constants declarations
  syntax Set ::= "collectConstants" "(" K ")" [function]

  // ConstSmtlib: booleans
  rule collectConstants(true) => .Set
  rule collectConstants(false) => .Set
  rule collectConstants(symBool(I:Int)) => SetItem(symBool(I))
  rule collectConstants(symBool(Var:Id)) => SetItem(symBool(Var:Id))

  rule collectConstants(notBool B:Bool)  => collectConstants(B)
  rule collectConstants(B1:Bool ==Bool B2:Bool)  => collectConstants(B1) collectConstants(B2)
  rule collectConstants(B1:Bool =/=Bool B2:Bool) => collectConstants(B1) collectConstants(B2)
  rule collectConstants(B1:Bool andBool B2:Bool) => collectConstants(B1) collectConstants(B2)
  rule collectConstants(B1:Bool orBool B2:Bool)  => collectConstants(B1) collectConstants(B2)
  rule collectConstants(B1:Bool xorBool B2:Bool) => collectConstants(B1) collectConstants(B2)
  rule collectConstants(B1:Bool impliesBool B2:Bool) => collectConstants(B1) collectConstants(B2)

  // collectConstants: integers
  rule collectConstants(symInt(I:Int)) => SetItem(symInt(I))
  rule collectConstants(symInt(Var:Id)) => SetItem(symInt(Var:Id))
  rule collectConstants(I:#Int) => .Set

  rule collectConstants(I1:Int <Int I2:Int)   => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int <=Int I2:Int)  => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int >Int I2:Int)   => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int >=Int I2:Int)  => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int ==Int I2:Int)  => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int =/=Int I2:Int) => collectConstants(I1) collectConstants(I2)

  rule collectConstants(I1:Int +Int I2:Int)   => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int -Int I2:Int)   => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int *Int I2:Int)  => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int /Int I2:Int)   => collectConstants(I1) collectConstants(I2)
  rule collectConstants(I1:Int %Int I2:Int)  => collectConstants(I1) collectConstants(I2)
  rule collectConstants(minInt(I1:Int, I2:Int))  => collectConstants(I1) collectConstants(I2)

  rule collectConstants(select A:Array I:Int) => collectConstants(A) collectConstants(I)
  rule collectConstants(store  A:Array P:Int I:Int) => collectConstants(A) collectConstants(P) collectConstants(I)

  // collectConstans: arrays
  rule collectConstants(symArray(X:Id)) => SetItem("(declare-fun " +String Id2String(X) +String " () (Array Int Int))")

  // collectConstants: fol
  rule collectConstants((forall (Is:IntList)(B:Bool))) => collectConstants(B)
  rule collectConstants(notFol F:Fol) => collectConstants(F)
  rule collectConstants(F1:Fol orFol F2:Fol)  => collectConstants(F1) collectConstants(F2)
  rule collectConstants(F1:Fol andFol F2:Fol) => collectConstants(F1) collectConstants(F2)

endmodule
module SMT-SYNTAX-HOOKS

  syntax SmtResponse ::= "sat"
                       | "unsat"
               | "unknown"
               | "model" "(" Map ")"

  syntax SmtResponse ::= "checkSat" "(" K ")" [function]
                       | "getModel" "(" K ")" [function]

  syntax Bool ::= SmtResponse "=/=" SmtResponse
        | SmtResponse "==" SmtResponse
endmodule

module SMT-HOOKS
  imports #SMT
  imports SMT-SYNTAX-HOOKS
  imports SMTLIB-CONVERSION
  imports S-EXP-PARSER


  // hook to #smtCall
  syntax String ::= "smtCall" "(" String ")" [function, hook(#SMT:#smtCall_)]

  // parse SMT response
  syntax SmtResponse ::= "parseSmtResponse" "(" String ")" [function]

  // basic smt interface rules
  rule checkSat(F) => parseSmtResponse( smtCall ( "(set-logic AUFNIRA) (define-fun minInt ((x1 Int) (x2 Int)) Int (ite (<= x1 x2) x1 x2)) " +String  createSmtCommand(collectConstants(F), Smtlib(F)) +String " (check-sat)"))
  rule getModel(F) => parseSmtResponse( smtCall ( "(set-logic AUFNIRA) (define-fun minInt ((x1 Int) (x2 Int)) Int (ite (<= x1 x2) x1 x2))" +String  createSmtCommand(collectConstants(F), Smtlib(F)) +String " (check-sat) (get-model)"))


  // main smt responses
  rule parseSmtResponse(S:String) => sat when trim(S) ==String "sat"
  rule parseSmtResponse(S:String) => unsat when trim(S) ==String "unsat"
  rule parseSmtResponse(S:String) => unknown when trim(S) ==String "unknown" orBool trim(S) ==String "unsupported"


  // parse SEXPRESSIONS
/*  rule parseSmtResponse(S:String) => getModelMap(parseSExpression("(" +String trim(replaceAll(S, "\n", " ")) +String ")"))
       when (trim(S) =/=String "sat\n") andBool
               (trim(S) =/=String "unsat\n") andBool
          (trim(S) =/=String "unknown\n") andBool
        (trim(S) =/=String "unsupported\n") [function, anywhere]
*/

  // create model
//  syntax SmtResponse ::= "getModelMap" "(" SExpression ")" [function]

//  rule getModelMap(S1:SExpressions [ stoken("define-fun") stoken(Var:String) T:Token stoken(Type:String) S:SExpressions stoken(Val:String) ] S2:SExpressions) => Var |-> Val [anywhere]


  // utils
  syntax String ::= "createSmtCommand" "(" Set "," String ")" [function]
          | "declareConstants" "(" Set ")" [function]

  rule createSmtCommand(S:Set, Assert:String) => declareConstants(S) +String " " +String " (assert " +String Assert +String ")"
  rule declareConstants(.Set) => " "
  rule declareConstants(SetItem(symInt (V:Int)) Rest:Set) => "(declare-const var" +String Int2String(V) +String " Int)" +String " " +String declareConstants(Rest)
  rule declareConstants(SetItem(symInt (V:Id )) Rest:Set) => "(declare-const " +String Id2String(V) +String " Int)" +String " " +String declareConstants(Rest)
  rule declareConstants(SetItem(symBool(V:Int)) Rest:Set) => "(declare-const var" +String Int2String(V) +String " Int)" +String " " +String declareConstants(Rest)
  rule declareConstants(SetItem(symBool(V:Id )) Rest:Set) => "(declare-const " +String Id2String(V) +String " Int)" +String " " +String declareConstants(Rest)
  rule declareConstants(SetItem(S:String) Rest:Set) => S +String " " +String declareConstants(Rest)
endmodule

module S-EXP-PARSER
  syntax Token ::= SExpression | Int | Id | Float | String
  syntax SExpressions ::= List{Token, ",Token"} [strict]
  syntax SExpression  ::= "[" SExpressions "]"

  syntax SExpression  ::= "parseSExpression" "(" String ")" [function]
  syntax SExpression  ::= "scan" "(" String  ")" [function]
  syntax SExpressions ::= "scanList" "(" String ")" [function]

  syntax Token ::= "stoken" "(" String ")" [function]
  syntax String ::= "getBalanced" "(" String ")" [function]
  syntax Int ::= "getFirstBalancedClosedParen" "(" String "," Int ")" [function]
             | "getFirstBalancedClosedParen" "(" String "," Int "," Int "," Int ")" [function]

  rule parseSExpression(S:String) => scan(trim(replaceAll(replaceAll(S,"(", " ( "), ")", " ) ")))

  rule scan(S:String) => [ scanList(trim(substrString(S, 1, lengthString(S) -Int 2))) ]
       when (substrString(S, 0, 1) ==String "(") andBool (substrString(S, lengthString(S) -Int 1, 1) ==String ")" )

  rule scanList(S:String) => stoken(substrString(S, 0, findString(S," ",0))) ,Token scanList(trim(substrString(S, findString(S," ",0) +Int 1, lengthString(S))))
       when (substrString(S, 0, 1) =/=String "(") andBool S =/=String "" andBool findString(S, " ", 0) =/=Int -1

  rule scanList(S:String) => scan(trim(substrString(S, 0, getFirstBalancedClosedParen(S, 0)))) ,Token
       scanList(trim(substrString(S, getFirstBalancedClosedParen(S, 0) +Int 1, lengthString(S))))
       when (substrString(S, 0, 1) ==String  "(")
  rule scanList("") => .


  rule getFirstBalancedClosedParen(S:String, Position:Int, Open:Int, Closed:Int) =>
       getFirstBalancedClosedParen(S:String, findString(S, ")", Position) +Int 1,
                                countAllOccurences(substrString(S, 0, findString(S,")",Position +Int 1)), "("),
                         countAllOccurences(substrString(S, 0, findString(S,")",Position +Int 1) +Int 1), ")"))
       when Position =/=Int 0 andBool Open =/=Int Closed  andBool Position <Int lengthString(S)
  rule getFirstBalancedClosedParen(S:String, 0) =>
       getFirstBalancedClosedParen(S:String, findString(S, ")", 0) +Int 1,
                                countAllOccurences(substrString(S, 0, findString(S,")",0) +Int 1), "("),
                         countAllOccurences(substrString(S, 0, findString(S,")",0) +Int 1), ")"))
    when countAllOccurences(substrString(S, 0, findString(S,")",0)), "(") >Int countAllOccurences(substrString(S, 0, findString(S,")",0)), ")")
  rule getFirstBalancedClosedParen(S:String, Position:Int, Count:Int, Count) => Position

  rule stoken(S:String) => . when trim(S) ==String ""


  // equalities
  rule sat =/= unsat => true
  rule unsat =/= sat => true
  rule unknown =/= unsat => true
  rule unsat =/= unknown => true
  rule unknown =/= sat => true
  rule sat =/= unknown => true

endmodule
