require "builtins/builtins.k"
require "builtins/int-symbolic.k"
require "builtins/bool-symbolic.k"

module SMTLIB
  imports BUILTIN-HOOKS
  imports INT-SYMBOLIC
  imports BOOL-SYMBOLIC  

  syntax String ::= "Smtlib" "(" Bool ")"
		  | "Smtlib" "(" Int ")"
		  | "ConstSmtlib" "(" Bool ")"
		  | "ConstSmtlib" "(" Int ")"

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
  rule Smtlib(I:Int) => Int2String(I) when notBool(isIntSymbolic(I)) [anywhere]
  rule Smtlib(symInt(I:Int)) => "var" +String Int2String(I) [anywhere]

  rule Smtlib(I1:Int <Int I2:Int) => "(< " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int <=Int I2:Int) => "(<= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int >Int I2:Int) => "(> " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int >=Int I2:Int) => "(> " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int ==Int I2:Int) => "(= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String ")" [anywhere]
  rule Smtlib(I1:Int =/=Int I2:Int) => "(not (= " +String Smtlib(I1) +String  " " +String Smtlib(I2) +String "))" [anywhere]




  //@ Collecting constants declarations

  // ConstSmtlib: booleans
  rule ConstSmtlib(true) => "" [anywhere]
  rule ConstSmtlib(false) => "" [anywhere]
  rule ConstSmtlib(symBool(I:Int)) => "(declare-const " +String "var" +String Int2String(I) +String " Bool)" [anywhere]
  
  rule ConstSmtlib(B1:Bool ==Bool B2:Bool)  => ConstSmtlib(B1) +String " " +String ConstSmtlib(B2) [anywhere]
  rule ConstSmtlib(B1:Bool =/=Bool B2:Bool) => ConstSmtlib(B1) +String " " +String ConstSmtlib(B2) [anywhere]
  rule ConstSmtlib(B1:Bool andBool B2:Bool) => ConstSmtlib(B1) +String " " +String ConstSmtlib(B2) [anywhere]
  rule ConstSmtlib(B1:Bool orBool B2:Bool)  => ConstSmtlib(B1) +String " " +String ConstSmtlib(B2) [anywhere]
  rule ConstSmtlib(B1:Bool xorBool B2:Bool) => ConstSmtlib(B1) +String " " +String ConstSmtlib(B2) [anywhere]

  // ConstSmtlib: integers
  rule ConstSmtlib(symInt(I:Int)) => "(declare-const " +String "var" +String Int2String(I) +String " Int)" [anywhere]
 
  rule ConstSmtlib(I1:Int <Int I2:Int)   => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]
  rule ConstSmtlib(I1:Int <=Int I2:Int)  => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]
  rule ConstSmtlib(I1:Int >Int I2:Int)   => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]
  rule ConstSmtlib(I1:Int >=Int I2:Int)  => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]
  rule ConstSmtlib(I1:Int ==Int I2:Int)  => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]
  rule ConstSmtlib(I1:Int =/=Int I2:Int) => ConstSmtlib(I1) +String  " " +String ConstSmtlib(I2) [anywhere]

endmodule

module SMT
  imports SMTLIB

  syntax K ::= "#checksat" "(" Bool ")"

  rule #checksat(B:Bool) => #tcpRequest("smt#" +String ConstSmtlib(B) +String " (assert " +String Smtlib(B) +String ") (check-sat)#") [function]

  syntax Bool ::= "toSmtlib" "(" List ")" [function]
  rule toSmtlib(ListItem(B:Bool) Rest:List) => B andBool toSmtlib(Rest) [anywhere]
  rule toSmtlib(.List) => true [anywhere]

endmodule
