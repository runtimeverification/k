require "string.k"

module LCID-SYNTAX-HOOKS
	syntax LCId ::= Token{[a-z][\_a-zA-Z0-9]*}       [notInRules, regex("(?<![A-Za-z0-9\\_])[a-z\\_][A-Za-z0-9\\_]*")]
endmodule

module LCID-HOOKS
  imports LCID-SYNTAX-HOOKS
  imports STRING-HOOKS
  imports K

	syntax String ::= "LCId2String" "(" LCId ")"         [function, hook(#CONVERSION:token2string), klabel(LCId2String)]
	syntax LCId ::= "String2LCId" "(" String ")"         [function, hook(#CONVERSION:string2id), klabel(String2LCId)]
	rule LCId2String(X:LCId) => #tokenToString(X)
	rule String2LCId(S:String) => #parseToken("LCId", S)

	syntax LCId ::= freshLCId(Int)	[freshGenerator, function]
	rule freshLCId(I:Int) => String2LCId("new_" +String Int2String(I))
endmodule

