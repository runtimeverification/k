require /modules/builtins/id
require /modules/builtins/int
require /modules/builtins/float

module STRING-SYNTAX-HOOKS
  syntax String ::= #String
end module

module STRING-HOOKS
  imports STRING-SYNTAX-HOOKS
  imports INT-HOOKS
  imports FLOAT-HOOKS
  imports ID-HOOKS

---  declare _+String_ : String String -> String
  syntax String ::= String "+String" String
        [function prec(33) gather(E e) latex "{#1}+_{\scriptstyle\it String}{#2}"
         hook(#STRING:_+String_)]
---  declare _==String_ : String String -> Bool
  syntax Bool ::= String "==String" String
        [function hook(#STRING:_==String_)]

---  declare lengthString : String -> Int
  syntax Int ::= "lengthString" "(" String ")" 
        [function klabel(lengthString) hook(#STRING:lengthString)]

---  declare charString : Int -> String
  syntax String ::= "charString" "(" Int ")"
        [function klabel(charString) hook(#STRING:charString)]
---  declare asciiString : String -> Int
  syntax Int ::= "asciiString" "(" String ")"
        [function klabel(asciiString) hook(#STRING:asciiString)]

---  declare substrString : String Int Int -> String
  syntax String ::= "substrString" "(" String "," Int "," Int")" 
        [function klabel(substrString) hook(#STRING:substrString)]

---  declare Float2String : Float -> String
  syntax String ::= "Float2String" "(" Float ")"
        [function klabel(Float2String) hook(#CONVERSION:float2String)]
---  declare String2Float : String -> Float
  syntax Float ::= "String2Float" "(" String ")" 
        [function klabel(String2Float) hook(#CONVERSION:string2Float)]
---  declare String2Int : String -> Int
  syntax Int ::= "String2Int" "(" String ")"
        [function klabel(String2Int) hook(#CONVERSION:string2Int)]
---  declare Int2String : Int -> String
  syntax String ::= "Int2String" "(" Int ")"
        [function klabel(Int2String) hook(#CONVERSION:int2String)]
---  declare Id2String : Id -> String
  syntax String ::= "Id2String" "(" Id ")"
        [function klabel(Id2String) hook(#CONVERSION:id2String)]
---  declare String2Id : String -> Id
  syntax Id ::= "String2Id" "(" String ")"
        [function klabel(String2Id) hook(#CONVERSION:string2Id)]

---  declare _=/=String_ : String String -> Bool
  syntax Bool ::= String "=/=String" String      [function]
  define S1:String =/=String S2:String => notBool(S1 ==String S2)

  sort Char
---  declare isChar : String -> Bool
  syntax Bool ::= "isChar" "(" String ")"        [function klabel(isChar)]
  define isChar(S:String) => lengthString(S) ==Int 1 

---  declare #isWhiteSpace : Char -> Bool 
  syntax Bool ::= "#isWhiteSpace" "(" Char ")"   [function klabel(#isWhiteSpace)]
  define #isWhiteSpace(C:Char) 
      => (asciiString(C) >=Int 9 andBool asciiString(C) <=Int 13)  
           orBool (C ==String " ")

---  declare #isDigit : Char -> Bool
  syntax Bool ::= "#isDigit" "(" Char ")"        [function klabel(#isDigit)]
  define #isDigit(C) 
      => (asciiString(C) >=Int asciiString("0")) 
           andBool (asciiString(C) <=Int asciiString("9")) 
end module



