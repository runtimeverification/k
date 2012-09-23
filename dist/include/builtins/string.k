require "id.k"
require "int.k"
require "float.k"

module STRING-SYNTAX-HOOKS
  imports #STRING-INTERFACE
  syntax String ::= #String
endmodule

module STRING-HOOKS
  imports STRING-SYNTAX-HOOKS
  imports INT-HOOKS
  imports FLOAT-HOOKS
  imports ID-HOOKS


  syntax String ::= String "+String" String	[function, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(#STRING:_+String_)]

  syntax Bool ::= String "==String" String [function, left, hook(#STRING:_==String_)]

  syntax Int ::= "lengthString" "(" String ")" [function, klabel(lengthString), hook(#STRING:lengthString)]
  syntax String ::= "charString" "(" Int ")"   [function, klabel(charString), hook(#STRING:charString)]
  syntax Int ::= "asciiString" "(" String ")"  [function, klabel(asciiString), hook(#STRING:asciiString)]

  syntax String ::= "substrString" "(" String "," Int "," Int ")" [function, klabel(substrString), hook(#STRING:substrString)]
  syntax Int ::= "findString" "(" String "," String "," Int ")" [function, klabel(findString), hook(#STRING:findString)]

  syntax String ::= "Float2String" "(" Float ")" [function, klabel(Float2String), hook(#CONVERSION:float2String)]
  syntax Float ::= "String2Float" "(" String ")" [function, klabel(String2Float), hook(#CONVERSION:string2Float)]
  syntax Int ::= "String2Int" "(" String ")"	 [function, klabel(String2Int), hook(#CONVERSION:string2Int)]
  syntax String ::= "Int2String" "(" Int ")"	 [function, klabel(Int2String), hook(#CONVERSION:int2String)]
  syntax String ::= "Id2String" "(" Id ")"		 [function, klabel(Id2String), hook(#CONVERSION:id2String)]
  syntax Id ::= "String2Id" "(" String ")"		 [function, klabel(String2Id), hook(#CONVERSION:string2Id)]


  syntax String ::= "KLabel2String" "(" KLabel ")"  [function, klabel(KLabel2String)]
  syntax KLabel ::= "String2KLabel" "(" String ")" [function]

  syntax String ::= "replaceAll" "(" String "," String "," String ")" [function]
  syntax String ::= "replace" "(" String "," String "," String "," Int ")" [function]
  syntax String ::= "replaceFirst" "(" String "," String "," String ")" [function]
  syntax Int ::= "countAllOccurences" "(" String "," String ")" [function]
  
  syntax String ::=  "trim" "(" String ")" [function]
  syntax String ::= "ltrim" "(" String ")" [function]
  syntax String ::= "rtrim" "(" String ")" [function]
  
  syntax Bool ::= String "=/=String" String      [function, left]
  rule S1:String =/=String S2:String => notBool(S1 ==String S2) [function, anywhere]

  syntax String ::= String "<String" String [function, hook(#STRING:_<String_)]
                  | String "<=String" String [function]
                  | String ">String" String [function]
                  | String ">=String" String [function]

  rule S1:String <=String S2:String => notBool(S2 <String S1) [function, anywhere]
  rule S1:String >String S2:String => S2 <String S1 [function, anywhere]
  rule S1:String >=String S2:String => notBool(S1 <String S2) [function, anywhere]

  syntax Char ::= "dummyChar"

  rule isChar(S:String) => lengthString(S) ==Int 1 [function, anywhere]

  syntax Bool ::= "#isWhiteSpace" "(" Char ")"   [function, klabel(#isWhiteSpace)]
  rule #isWhiteSpace(C:Char)
      => (asciiString(C) >=Int 9 andBool asciiString(C) <=Int 13)  
           orBool (C ==String " ") [function, anywhere]

  syntax Bool ::= "#isDigit" "(" Char ")"        [function, klabel(#isDigit)]
  rule #isDigit(C:Char) 
      => (asciiString(C) >=Int asciiString("0")) 
           andBool (asciiString(C) <=Int asciiString("9")) [function, anywhere]

  rule countAllOccurences(Source:String, ToCount:String) => 0 
			when findString(Source, ToCount, 0) <Int 0 [function, anywhere]
  rule countAllOccurences(Source:String, ToCount:String) => 1 +Int countAllOccurences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount), lengthString(Source)), ToCount) 
			when findString(Source, ToCount, 0) >=Int 0 [function, anywhere]
			
  rule replaceFirst(Source:String, ToReplace:String, Replacement:String) => substrString(Source, 0, findString(Source, ToReplace, 0))
				+String Replacement +String substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source)) 
				when findString(Source, ToReplace, 0) >=Int 0 [function, anywhere]
  rule replaceFirst(Source:String, ToReplace:String, Replacement:String) => Source 
		when findString(Source, ToReplace, 0) <Int 0 [function, anywhere]
  
  
  rule replace(Source:String, ToReplace:String, Replacement:String, Count:Int) => replace(replaceFirst(Source, ToReplace, Replacement), ToReplace, Replacement, Count -Int 1) 
		when Count >Int 0 [function, anywhere]
  rule replace(Source, ToReplace, Replacement, 0) => Source [function, anywhere]
  rule replaceAll(Source, ToReplace, Replacement) => replace(Source, ToReplace, Replacement, countAllOccurences(Source, ToReplace)) [function, anywhere] 

  rule ltrim(S:String) => replaceFirst(S, " ", "") when findString(S, " ", 0) ==Int 0 [function, anywhere]
  rule ltrim(S:String) => S when findString(S, " ", 0) =/=Int 0 [function, anywhere]

  rule rtrim(S:String) => rtrim(substrString(S,0, lengthString(S) -Int 1)) when substrString(S, lengthString(S) -Int 1, lengthString(S)) ==String " " [function, anywhere]
  rule rtrim(S:String) => S when substrString(S, lengthString(S) -Int 1, lengthString(S)) =/=String " " [function, anywhere]
  
  rule trim(S) => ltrim(rtrim(S)) [function, anywhere]


  syntax K ::= "#parseToken" "(" String "," String ")"  [function]
  rule #parseToken("Int",S:String) => (String2Int(S +String "0") /Int 10) [anywhere]
  rule #parseToken("Float",S:String) => (String2Float(S))  [anywhere]
  rule #parseToken("String",S:String) => (S)  [anywhere]
  rule #parseToken("Id",S:String) => (String2Id(S))  [anywhere]

  rule String2Int("00") => 0  [anywhere]

   

endmodule
