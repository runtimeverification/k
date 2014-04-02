require "string.k"

module ID-SYNTAX-HOOKS
  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}   [notInRules, regex("(?<![A-Za-z\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports STRING-HOOKS
  imports K

  syntax String ::= "Id2String" "(" Id ")"		 [function, hook(#CONVERSION:token2string), klabel(Id2String)]
  syntax Id ::= "String2Id" "(" String ")"		 [function, klabel(String2Id)]
  rule Id2String(X:Id) => #tokenToString(X)
  rule String2Id(S:String) => #parseToken("Id", S)
endmodule
