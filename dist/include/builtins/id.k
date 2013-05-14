require "string.k"

module ID-SYNTAX-HOOKS
  imports #ID-INTERFACE
  syntax Id ::= #Id 
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports STRING-HOOKS
  imports K

  //syntax String ::= "Id2String" "(" Id ")"		 [function, klabel(Id2String), hook(#CONVERSION:id2String)]
  //syntax Id ::= "String2Id" "(" String ")"		 [function, klabel(String2Id), hook(#CONVERSION:string2Id)]
  syntax String ::= "Id2String" "(" Id ")"		 [function, klabel(Id2String)]
  syntax Id ::= "String2Id" "(" String ")"		 [function, klabel(String2Id)]
  rule Id2String(X:Id) => #tokenToString(X)
  rule String2Id(S:String) => #parseToken("Id", S)

  // Check if an identifier is capitalized.  Useful for languages like Prolog
  //syntax CapitalizedId ::= "A-Dummy-Capitalized-Id-Just-Because-We-Do-Not-Allow-Empty-Productions-Yet"
  //rule isCapitalizedId(X) => true
  //  when asciiString(substrString(Id2String(X),0,1)) <Int 96
  //rule isCapitalizedId(#symId(_)) => true

  //rule #parseToken("#Id",S:String) => (String2Id(S))
  //rule #parseToken("Id",S:String) => (String2Id(S))
endmodule
