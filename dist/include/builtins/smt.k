require "builtins/builtins.k"
require "builtins/int-symbolic.k"
require "builtins/bool-symbolic.k"

module SMTLIB-CONVERSION
  imports BUILTIN-HOOKS
  imports INT-SYMBOLIC
  imports BOOL-SYMBOLIC  


  // convert Bool to smtlib
  syntax String ::= "Smtlib" "(" Bool ")"
          | "Smtlib" "(" Int ")"

  // Smtlib: booleans  
  rule Smtlib(false) => "false" [anywhere]
  rule Smtlib(true)  => "true"  [anywhere]
  rule Smtlib(symBool(I:Int)) => "var" +String Int2String(I) [anywhere]
  rule Smtlib(symBool(Var:Id)) => Id2String(Var) [anywhere]
  
  rule Smtlib(B1:Bool ==Bool B2:Bool) => "(= " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool =/=Bool B2:Bool) => "(not (= " +String Smtlib(notBool B1) +String  " " +String Smtlib(notBool B2) +String "))" [anywhere]
  rule Smtlib(B1:Bool andBool B2:Bool) => "(and " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool orBool B2:Bool) => "(or " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool xorBool B2:Bool) => "(xor " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(notBool B:Bool) => "(not " +String Smtlib(B) +String ")" [anywhere]

  // Smtlib: integers
  rule Smtlib(I:#Int) => Int2String(I) [anywhere]
  rule Smtlib(symInt(I:Int)) => "var" +String Int2String(I) [anywhere]
  rule Smtlib(symInt(Var:Id)) => Id2String(Var) [anywhere]

  rule Smtlib(I1:Int +Int I2:Int) => "(+ " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int *Int I2:Int) => "(* " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int /Int I2:Int) => "(/ " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int -Int I2:Int) => "(- " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int %Int I2:Int) => "(% " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  
  rule Smtlib(I1:Int <Int I2:Int) => "(< " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int <=Int I2:Int) => "(<= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int >Int I2:Int) => "(> " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int >=Int I2:Int) => "(> " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int ==Int I2:Int) => "(= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int =/=Int I2:Int) => "(not (= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String "))" [anywhere]


  //@ Collecting constants declarations
  
  syntax Set ::= "collectConstants" "(" Bool ")"
               | "collectConstants" "(" Int ")"

  // ConstSmtlib: booleans
  rule collectConstants(true) => .Set [anywhere]
  rule collectConstants(false) => .Set [anywhere]
  rule collectConstants(symBool(I:Int)) => SetItem(symBool(I)) [anywhere]
  rule collectConstants(symBool(Var:Id)) => SetItem(symBool(Var:Id)) [anywhere]
  
  rule collectConstants(notBool B:Bool)  => collectConstants(B) [anywhere]
  rule collectConstants(B1:Bool ==Bool B2:Bool)  => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool =/=Bool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool andBool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool orBool B2:Bool)  => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool xorBool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]

  // collectConstants: integers
  rule collectConstants(symInt(I:Int)) => SetItem(symInt(I)) [anywhere]
  rule collectConstants(symInt(Var:Id)) => SetItem(symInt(Var:Id)) [anywhere]
  rule collectConstants(I:#Int) => .Set [anywhere]
 
  rule collectConstants(I1:Int <Int I2:Int)   => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int <=Int I2:Int)  => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int >Int I2:Int)   => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int >=Int I2:Int)  => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int ==Int I2:Int)  => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int =/=Int I2:Int) => collectConstants(I1) collectConstants(I2) [anywhere]

  rule collectConstants(I1:Int +Int I2:Int)   => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int -Int I2:Int)   => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int *Int I2:Int)  => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int /Int I2:Int)   => collectConstants(I1) collectConstants(I2) [anywhere]
  rule collectConstants(I1:Int %Int I2:Int)  => collectConstants(I1) collectConstants(I2) [anywhere]
  
endmodule

module SMT-IO
  imports URIS

  syntax Int ::= "#openSmtSession" 
  syntax K ::= "#closeSmtSession" "(" Int ")"
  syntax String ::= "#sendSmtCommand" "(" Int "," String ")"

  rule #openSmtSession => String2Int((#tcpRequest("open#" +String "smt" +String "#"))) [function, anywhere]
  rule #closeSmtSession(I:Int) => #close(I) [function, anywhere]
  rule #sendSmtCommand(I:Int, S:String) => #tcpRequest("smt#" +String Int2String(I) +String "#" +String S +String "#") [function, anywhere]

endmodule

module SMT
  imports SMT-IO
  imports SMTLIB-CONVERSION

  syntax K ::= "checkSat" "(" Bool ")" [function]
  syntax Map ::= "getModel" "(" Bool ")" [function]

  // check-sat for boolean formula
  syntax K ::= "#checkSat" "(" Int "," String ")" [function]
             | "#smt" "(" Int "," Set "," String ")" [function]
  
  rule checkSat(B:Bool) => #smt(#openSmtSession, collectConstants(B), Smtlib(B) ) [anywhere]
  
  rule #smt(I:Int, .Set, S:String) => #checkSat(I, #sendSmtCommand(I, "(assert " +String S +String ")")) [anywhere]
  rule #checkSat(I:Int, "success") => #sendSmtCommand(I, "(check-sat)") [anywhere]
  rule #smt(I:Int, SetItem(symInt(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Int)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, SetItem(symBool(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Bool)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, SetItem(symInt(Var:Id) =>  #sendSmtCommand(I,"(declare-const " +String Id2String(Var) +String " Int)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, SetItem(symBool(Var:Id) =>  #sendSmtCommand(I,"(declare-const " +String Id2String(Var) +String " Bool)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, (SetItem("success") => .Set) _:Set, _:String) [anywhere]


  // get-model for boolean formula
  syntax Map ::= "#model" "(" Int "," Set "," String ")"
  syntax Map ::= "#get" "(" Int "," String ")"
  
  rule getModel(B:Bool) => #model(#openSmtSession, collectConstants(B), Smtlib(B)) [anywhere]

  rule #model(I:Int, .Set, S:String) => #get(I, #checkSat(I, #sendSmtCommand(I, "(assert " +String S +String ")"))) [anywhere]
  rule #get(I:Int, "sat") => toMap(#sendSmtCommand(I, "(get-model)")) [anywhere]
  rule #model(I:Int, SetItem(symInt(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Int)")) _:Set, _:String) [anywhere]
  rule #model(I:Int, SetItem(symBool(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Bool)")) _:Set, _:String) [anywhere]
  rule #model(I:Int, SetItem(symInt(Var:Id) =>  #sendSmtCommand(I,"(declare-const " +String Id2String(Var) +String " Int)")) _:Set, _:String) [anywhere]
  rule #model(I:Int, SetItem(symBool(Var:Id) =>  #sendSmtCommand(I,"(declare-const " +String Id2String(Var) +String " Bool)")) _:Set, _:String) [anywhere]
  rule #model(I:Int, (SetItem("success") => .Set) _:Set, _:String) [anywhere]

  syntax Map ::= "toMap" "(" String ")"
  syntax MapItem ::= "processToMap" "(" String ")"

  rule toMap(S:String) => processToMap( substrString(S, 1, findString(S , "$", 0) -Int 1) )
                          toMap(substrString(S, findString(S, "$", 0) +Int 1, lengthString(S)))
                          when S =/=String "" [anywhere]
  rule toMap("") => . [anywhere]

  syntax MapItem ::= "castKey" "(" String "," String ")"
                    | "castToMapItem" "(" String "," String "," String ")"
                    
  rule processToMap(S:String) => castKey(substrString(S, 0, findString(S, "#", 0) ), substrString(S, findString(S, "#", 0) +Int 1, lengthString(S))) [anywhere]
  rule castKey(Key:String, S:String) => castToMapItem(Key, substrString(S, 0, findString(S, "#", 0)), substrString(S, findString(S, "#", 0) +Int 1, lengthString(S))) [anywhere]

  rule castToMapItem(Key:String, "Int", Value:String) => String2Id(Key) |-> String2Int(Value) [anywhere]
  rule castToMapItem(Key:String, "Bool", Value:String) => String2Id(Key) |-> String2Bool(Value) [anywhere]

endmodule
