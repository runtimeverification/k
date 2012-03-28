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

  declare _+String_ : String String -> String
        [prec(33) gather(E e) latex "{#1}+_{\scriptstyle\it String}{#2}"
         hook(#STRING:_+String_)]
  declare _==String_ : String String -> Bool [hook(#STRING:_==String_)]

  declare lengthString : String -> Int [hook(#STRING:lengthString)]

  declare charString : Int -> String [hook(#STRING:charString)]
  declare asciiString : String -> Int [hook(#STRING:asciiString)]

  declare substrString : String Int Int -> String [hook(#STRING:substrString)]

  declare Float2String : Float -> String [hook(#CONVERSION:float2String)]
  declare String2Float : String -> Float [hook(#CONVERSION:string2Float)]
  declare String2Int : String -> Int [hook(#CONVERSION:string2Int)]
  declare Int2String : Int -> String [hook(#CONVERSION:int2String)]
  declare Id2String : Id -> String [hook(#CONVERSION:id2String)]
  declare String2Id : String -> Id [hook(#CONVERSION:string2Id)]

  declare _=/=String_ : String String -> Bool
  define S1:String =/=String S2:String => notBool(S1 ==String S2)

  declare #isWhiteSpace : String -> Bool 
  define #isWhiteSpace(C:String) 
      => (asciiString(C) >=Int 9 andBool asciiString(C) <=Int 13)  
           orBool (C ==String " ")
    when isChar(C)

  declare #isDigit : String -> Bool
  define #isDigit(C) 
      => (asciiString(C) >=Int asciiString("0")) 
           andBool (asciiString(C) <=Int asciiString("9")) 
    when isChar(C)

  declare isChar : String -> Bool
  define isChar(S:String) => lengthString(S) ==Int 1 
end module



