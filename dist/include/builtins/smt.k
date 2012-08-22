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
  
  rule Smtlib(B1:Bool ==Bool B2:Bool) => "(= " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool =/=Bool B2:Bool) => "(not (= " +String Smtlib(notBool B1) +String  " " +String Smtlib(notBool B2) +String "))" [anywhere]
  rule Smtlib(B1:Bool andBool B2:Bool) => "(and " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool orBool B2:Bool) => "(or " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(B1:Bool xorBool B2:Bool) => "(xor " +String Smtlib(B1) +String  " " +String Smtlib(B2) +String ")" [anywhere]
  rule Smtlib(notBool B:Bool) => "(not " +String Smtlib(B) +String ")" [anywhere]

  // Smtlib: integers
  rule Smtlib(I:#Int) => Int2String(I) [anywhere]
  rule Smtlib(symInt(I:Int)) => "var" +String Int2String(I) [anywhere]

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

  // ConstSmtlib: booleans
  rule collectConstants(true) => .Set [anywhere]
  rule collectConstants(false) => .Set [anywhere]
  rule collectConstants(symBool(I:Int)) => SetItem(symBool(I)) [anywhere]
  
  rule collectConstants(B1:Bool ==Bool B2:Bool)  => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool =/=Bool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool andBool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool orBool B2:Bool)  => collectConstants(B1) collectConstants(B2) [anywhere]
  rule collectConstants(B1:Bool xorBool B2:Bool) => collectConstants(B1) collectConstants(B2) [anywhere]

  // collectConstants: integers
  rule collectConstants(symInt(I:Int)) => SetItem(symInt(I)) [anywhere]
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

  syntax K ::= "#openSmtSession" 
			 | "#closeSmtSession" "(" Int ")"
  syntax String ::= "#sendSmtCommand" "(" Int "," String ")"

  rule #openSmtSession => String2Int((#tcpRequest("open#" +String "smt" +String "#"))) [function, anywhere]
  rule #closeSmtSession(I:Int) => #close(I) [function, anywhere]
  rule #sendSmtCommand(I:Int, S:String) => #tcpRequest("smt#" +String Int2String(I) +String "#" +String S +String "#") [function, anywhere]

endmodule

module SMT
  imports SMT-IO
  imports SMTLIB-CONVERSION

  syntax K ::= "checkSat" "(" Bool ")" [function]
  
  syntax K ::= "#checkSat" "(" Int "," String ")"
			 | "#smt" "(" Int "," Set "," String ")"
  
  rule checkSat(B:Bool) => #smt(#openSmtSession, collectConstants(B), Smtlib(B) ) [anywhere]
  
  rule #smt(I:Int, .Set, S:String) => #checkSat(I, #sendSmtCommand(I, "(assert " +String S +String ")")) [anywhere]
  rule #checkSat(I:Int, "success") => #sendSmtCommand(I, "(check-sat)") [anywhere]
  rule #smt(I:Int, SetItem(symInt(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Int)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, SetItem(symBool(V:Int) =>  #sendSmtCommand(I,"(declare-const var" +String Int2String(V) +String " Bool)")) _:Set, _:String) [anywhere]
  rule #smt(I:Int, (SetItem("success") => .Set) _:Set, _:String) [anywhere]
  
  syntax Bool ::= "toSmtlib" "(" List ")" [function]
  rule toSmtlib(ListItem(B:Bool) Rest:List) => B andBool toSmtlib(Rest) [anywhere]
  rule toSmtlib(.List) => true [anywhere]
  
endmodule
