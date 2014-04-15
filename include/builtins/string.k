// Copyright (C) 2014 K Team. All Rights Reserved.
require "int.k"
require "float.k"

module STRING-SYNTAX-HOOKS
  imports #STRING-INTERFACE
  syntax #String
  syntax String ::= #String
  // TODO(Radu): replace the above with bellow
  //   syntax String ::= Token{"\"" ((~[\"\n\r\\])|([\\]~[\n\r]))* "'"}

endmodule

module STRING-HOOKS
  imports STRING-SYNTAX-HOOKS
  imports INT-HOOKS
  imports FLOAT-HOOKS


  syntax String ::= String "+String" String	[function, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(#STRING:_+String_)]

  syntax Bool ::= String "==String" String [function, left, hook(#STRING:_==String_)]

  syntax Int ::= "lengthString" "(" String ")" [function, klabel(lengthString), hook(#STRING:lengthString)]
  syntax String ::= "chrChar" "(" Int ")"   [function, klabel(chrChar), hook(#STRING:chrChar)]
  syntax Int ::= "ordChar" "(" String ")"  [function, klabel(ordChar), hook(#STRING:ordChar)]

  syntax String ::= "substrString" "(" String "," Int "," Int ")" [function, klabel(substrString), hook(#STRING:substrString)]
  syntax Int ::= "findString" "(" String "," String "," Int ")" [function, klabel(findString), hook(#STRING:findString)]
  syntax Int ::= "rfindString" "(" String "," String "," Int ")" [function, klabel(rfindString), hook(#STRING:rfindString)]
  syntax Int ::= "findChar" "(" String "," String "," Int ")" [function, klabel(findChar), hook(#STRING:findChar)]
  syntax Int ::= "rfindChar" "(" String "," String "," Int ")" [function, klabel(rfindChar), hook(#STRING:rfindChar)]

  syntax String ::= "Float2String" "(" Float ")" [function, klabel(Float2String), hook(#CONVERSION:float2string)]
  syntax Float ::= "String2Float" "(" String ")" [function, klabel(String2Float), hook(#CONVERSION:string2float)]
  syntax Int ::= "String2Int" "(" String ")"	 [function, klabel(String2Int), hook(#CONVERSION:string2int)]
  syntax String ::= "Int2String" "(" Int ")"	 [function, klabel(Int2String), hook(#CONVERSION:int2string)]


  syntax String ::= "KLabel2String" "(" KLabel ")"  [function, klabel(KLabel2String)]
  syntax KLabel ::= "String2KLabel" "(" String ")" [function, cons(KLabel1String2KLabelSyn)]

  syntax String ::= "replaceAll" "(" String "," String "," String ")" [function]
  syntax String ::= "replace" "(" String "," String "," String "," Int ")" [function]
  syntax String ::= "replaceFirst" "(" String "," String "," String ")" [function]
  syntax Int ::= "countAllOccurences" "(" String "," String ")" [function]
  
  syntax String ::=  "trim" "(" String ")" [function]
  syntax String ::= "ltrim" "(" String ")" [function]
  syntax String ::= "rtrim" "(" String ")" [function]
  
  syntax Bool ::= String "=/=String" String      [function, left, hook(#STRING:_=/=String_)]
  rule S1:String =/=String S2:String => notBool(S1 ==String S2)

  syntax Bool ::= String "<String" String [function, hook(#STRING:_<String_)]
                | String "<=String" String [function, hook(#STRING:_<=String_)]
                | String ">String" String [function, hook(#STRING:_>String_)]
                | String ">=String" String [function, hook(#STRING:_>=String_)]

  syntax String ::= categoryChar(String) [function, hook(#STRING:categoryChar)]
                  | directionalityChar(String) [function, hook(#STRING:directionalityChar)]

  rule S1:String <=String S2:String => notBool(S2 <String S1)
  rule S1:String >String S2:String => S2 <String S1
  rule S1:String >=String S2:String => notBool(S1 <String S2)

  rule findChar(S1:String, S2:String, I:Int) => #if findString(S1, substrString(S2, 0, 1), I) ==Int -1 #then findChar(S1, substrString(S2, 1, lengthString(S2)), I) #else #if findChar(S1, substrString(S2, 1, lengthString(S2)), I) ==Int -1 #then findString(S1, substrString(S2, 0, 1), I) #else minInt(findString(S1, substrString(S2, 0, 1), I), findChar(S1, substrString(S2, 1, lengthString(S2)), I)) #fi #fi when S2 =/=String ""
  rule findChar(_, "", _) => -1
  rule rfindChar(S1:String, S2:String, I:Int) => maxInt(rfindString(S1, substrString(S2, 0, 1), I), rfindChar(S1, substrString(S2, 1, lengthString(S2)), I)) when S2 =/=String ""
  rule rfindChar(_, "", _) => -1

  syntax Char
  syntax String ::= "Char2String" "(" Char ")" [function]
  syntax Char ::= "String2Char" "(" String ")" [function]

  rule isChar(S:String) => lengthString(S) ==Int 1 [function, anywhere]

  syntax Bool ::= "#isWhiteSpace" "(" String ")"   [function, klabel(#isWhiteSpace)]
  rule #isWhiteSpace(C:String)
      => (ordChar(C) >=Int 9 andBool ordChar(C) <=Int 13)  
           orBool (C ==String " ") when isChar(C)

  syntax Bool ::= "#isDigit" "(" String ")"        [function, klabel(#isDigit)]
  rule #isDigit(C:String) 
      => (ordChar(C) >=Int ordChar("0")) 
           andBool (ordChar(C) <=Int ordChar("9")) when isChar(C)

  rule countAllOccurences(Source:String, ToCount:String) => 0 
			when findString(Source, ToCount, 0) <Int 0
  rule countAllOccurences(Source:String, ToCount:String) => 1 +Int countAllOccurences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount), lengthString(Source)), ToCount) 
			when findString(Source, ToCount, 0) >=Int 0
			
  rule replaceFirst(Source:String, ToReplace:String, Replacement:String) => substrString(Source, 0, findString(Source, ToReplace, 0))
				+String Replacement +String substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source)) 
				when findString(Source, ToReplace, 0) >=Int 0
  rule replaceFirst(Source:String, ToReplace:String, _:String) => Source 
		when findString(Source, ToReplace, 0) <Int 0
  
  
  rule replace(Source:String, ToReplace:String, Replacement:String, Count:Int) => 
       substrString(Source, 0, findString(Source, ToReplace, 0)) +String Replacement +String
       replace(substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source)), ToReplace, Replacement, Count -Int 1)
		when Count >Int 0
  rule replace(Source:K, _, _, 0) => Source
  rule replaceAll(Source:K, ToReplace:K, Replacement:K) => replace(Source, ToReplace, Replacement, countAllOccurences(Source, ToReplace))

  rule ltrim(S:String) => replaceFirst(S, " ", "") when findString(S, " ", 0) ==Int 0
  rule ltrim(S:String) => S when findString(S, " ", 0) =/=Int 0
  rule ltrim("") => ""

  rule rtrim(S:String) => rtrim(substrString(S,0, lengthString(S) -Int 1)) when substrString(S, lengthString(S) -Int 1, lengthString(S)) ==String " "
  rule rtrim(S:String) => S when substrString(S, lengthString(S) -Int 1, lengthString(S)) =/=String " "
  rule rtrim("") => ""
  
  rule trim(S:K) => ltrim(rtrim(S))

  syntax K ::= "#parseToken" "(" String "," String ")"  [function, klabel(#parseToken)]
  rule #parseToken("#Int",S:String) => String2Int(S)
  rule #parseToken("#Float",S:String) => (String2Float(S)) 
  rule #parseToken("#String",S:String) => (S) 
  rule #parseToken("Int",S:String) => String2Int(S)
  rule #parseToken("Float",S:String) => (String2Float(S)) 
  rule #parseToken("String",S:String) => (S) 
  rule #parseToken("Char",S:String) => (String2Char(S))

  syntax String ::= "#tokenToString" "(" K ")"    [function, klabel(#tokenToString), hook(#CONVERSION:token2string)]
endmodule
