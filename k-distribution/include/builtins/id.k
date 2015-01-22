// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "string.k"

module ID-SYNTAX-HOOKS
  syntax Id ::= Token{[A-Za-z\_][A-Za-z0-9\_]*}   [notInRules, regex("(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*")]
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports STRING-HOOKS
  imports K

  syntax String ::= "Id2String" "(" Id ")"         [function, hook(#CONVERSION:token2string), klabel(Id2String)]
  syntax Id ::= "String2Id" "(" String ")"         [function, hook(#CONVERSION:string2id), klabel(String2Id)]
  rule Id2String(X:Id) => #tokenToString(X)
  rule String2Id(S:String) => #parseToken("Id", S)

  syntax CamelCaseId
  syntax PascalCaseId
  rule isPascalCaseId(X:Id) => isUpperCase(substrString(#tokenToString(X), 0, 1))
  rule isCamelCaseId(X:Id) => isLowerCase(substrString(#tokenToString(X), 0, 1))

  syntax Id ::= freshId(Int)    [freshGenerator, function]
  rule freshId(I:Int) => String2Id("_" +String Int2String(I))
endmodule

