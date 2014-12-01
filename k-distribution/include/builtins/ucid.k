require "string.k"

module UCID-SYNTAX-HOOKS
	syntax UCId ::= Token{[A-Z][\_a-zA-Z0-9]*}       [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Z\\_][A-Za-z0-9\\_]*")]
endmodule

module UCID-HOOKS
  imports UCID-SYNTAX-HOOKS
  imports STRING-HOOKS
  imports K

	syntax String ::= "UCId2String" "(" UCId ")"         [function, hook(#CONVERSION:token2string), klabel(UCId2String)]
	syntax UCId ::= "String2UCId" "(" String ")"         [function, hook(#CONVERSION:string2id), klabel(String2UCId)]
	rule UCId2String(X:UCId) => #tokenToString(X)
	rule String2UCId(S:String) => #parseToken("UCId", S)

	syntax UCId ::= freshUCId(Int)	[freshGenerator, function]
	rule freshUCId(I:Int) => String2UCId("New_" +String Int2String(I))
endmodule

