// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module K-PRINTER
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS
  syntax Builtin ::= Int | String | Float | Id

  syntax String ::= "printSKExp" "(" K ")"  [function]
  rule printSKExp(B:Builtin) => printSKExpBuiltin(B)
  rule printSKExp(L:KLabel(Ks:KList))
    => "("
        +String KLabel2String(L)
        +String " "
        +String printSKExps(L(Ks))
        +String ")"
    when isBuiltin(L(Ks)) =/=K true

  syntax String ::= "printSKExps" "(" K ")"  [function]
  rule printSKExps(L:KLabel(K:K,,Ks:KList))
    => printSKExp(K) +String printSKExps(L(Ks))

  rule printSKExps(L:KLabel(.KList)) => ""


  syntax String ::= "printSKExpBuiltin" "(" K ")"  [function]
  rule printSKExpBuiltin(I:Int) => "((Int " +String Int2String(I) +String "))"
  rule printSKExpBuiltin(S:String) => "((String \"" +String S +String "\"))"
  rule printSKExpBuiltin(F:Float) => "((Float " +String Float2String(F) +String "))"
  rule printSKExpBuiltin(X:Id) => "((Id " +String Id2String(X) +String "))"
endmodule

module K-PARSER
  imports STRING-HOOKS
  imports K-EQUAL-HOOKS

  syntax KResult ::= "pair" "(" K "," String ")"
  syntax K ::= "parseSKExp" "(" String ")" [function]
  rule parseSKExp(S:String) => parseSKExpCheck(parseSKExpHelper(S))

  syntax K ::= "parseSKExpCheck" "(" K ")" [function]
  rule parseSKExpCheck(pair(K:K, "")) => K

  syntax K ::= "parseSKExpHelper" "(" String ")" [function]
  rule parseSKExpHelper(S:String)
    => parseSKExpHelper(substrString(S,0,1), ltrim(substrString(S,1, lengthString(S))))

  syntax K ::= "parseSKExpHelper" "(" String "," String ")"  [function]
  rule parseSKExpHelper("(", S:String)
    => parseSKExpLabel(substrString(S, 0, 1), S:String)

  syntax K ::= "parseSKExpLabel" "(" String "," String ")"  [function]
  rule parseSKExpLabel("(", S:String)
    => parseSKExpInjectedLabel(ltrim(substrString(S,1, lengthString(S))))
  rule parseSKExpLabel(S1:String, S2:String)
    => parseSKExpRealLabel(S2,findString(S2, " ", 0))
    when S1 =/=String "("

  syntax K ::= "parseSKExpRealLabel" "(" String "," Int ")" [function]
  rule parseSKExpRealLabel(S:String, I:Int)
    => parseSKExps(ltrim(substrString(S, I +Int 1, lengthString(S))), String2KLabel(substrString(S, 0, I))(.KList))

  syntax K ::= "parseSKExps" "(" String "," K ")"  [function]
  rule parseSKExps(S:String, K:K)
    => parseSKExps(substrString(S,0,1), S, K)

  syntax K ::= "parseSKExps" "(" String "," String "," K ")"  [function]
  rule parseSKExps(")", S, K) => pair(K, ltrim(substrString(S, 1, lengthString(S))))
  rule parseSKExps(S1:String, S2:String, K:K)
    => parseSKExpHelper(S2) ~> parseSKExps(HOLE, K)
    when S1 =/=String ")"

  rule (pair(K:K, S:String) => .K) ~> parseSKExps(HOLE => S, L:KLabel(_,,(.KList => K)))  [anywhere]

  syntax K ::= "parseSKExpInjectedLabel" "(" String ")" [function]
  rule parseSKExpInjectedLabel(S:String)
    => parseSKExpInjectedLabelType(S, findString(S, " ", 0))

  syntax K ::= "parseSKExpInjectedLabelType" "(" String "," Int ")" [function]
  rule parseSKExpInjectedLabelType(S:String, I:Int)
    => parseSKExpInjectedLabel(ltrim(substrString(S,0, I)), ltrim(substrString(S, I +Int 1, lengthString(S))))

  syntax K ::= "parseSKExpInjectedLabel" "(" String "," String ")" [function]
  rule parseSKExpInjectedLabel(S1:String, S2:String)
    => parseSKExpInjectedLabel(S1, S2, findString(S2, ")", 0))
    when S1 =/=String "String"

  syntax K ::= "parseSKExpInjectedLabel" "(" String "," String "," Int ")"
    [function]
  rule parseSKExpInjectedLabel(S1:String, S2:String, I:Int)
    => parseSKExps(ltrim(substrString(S2, I +Int 1, lengthString(S2))), #parseToken(S1, ltrim(substrString(S2, 0, I))))

  rule parseSKExpInjectedLabel("String", S:String)
    => parseSKExpInjectedString(S, findString(S,"\"",0))  [anywhere]

  syntax K ::= "parseSKExpInjectedString" "(" String "," Int ")" [function]
  rule parseSKExpInjectedString(S:String, 0)
    => parseSKExpInjectedString(S, 0, findString(S,"\"", 1))

  syntax K ::= "parseSKExpInjectedString" "(" String "," Int "," Int ")"
    [function]
  rule parseSKExpInjectedString(S:String, 0, I:Int)
    =>  parseSKExpInjectedString(S, 0, I, substrString(S,I -Int 1, 1))

  syntax K ::= "parseSKExpInjectedString" "(" String ","
                                              Int ","
                                              Int ","
                                              String ")"
    [function]
  rule parseSKExpInjectedString(S:String, 0, I:Int, "\\")
    => parseSKExpInjectedString(S, 0, findString(S,"\"",I +Int 1))
  rule parseSKExpInjectedString(S1:String, 0, I:Int, S2:String)
    => parseSKExps(ltrim(substrString(S1, findString(S1, ")", I +Int 1) +Int 1, lengthString(S1))), #parseToken("String", substrString(S1, 1, I -Int 1)))
    when S2 =/=String "\\"
endmodule
