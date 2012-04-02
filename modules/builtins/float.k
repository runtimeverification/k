require /modules/builtins/bool
require /modules/builtins/int
module FLOAT-SYNTAX-HOOKS
  syntax Float ::= #Float
end module

module FLOAT-HOOKS
  imports FLOAT-SYNTAX-HOOKS
  imports BOOL-HOOKS
  imports INT-HOOKS
  imports K

  declare _+Float_ : Float Float -> Float
      [prec(33) gather(E e) latex "{#1}\mathrel{+_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_+Float_)]

  declare _-Float_ : Float Float -> Float
      [prec(33) gather(E e) latex "{#1}\mathrel{-_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_-Float_)]

  declare _*Float_ : Float Float -> Float
      [prec(31) gather(E e) latex "{#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_*Float_)]

  declare _/Float_ : Float Float -> Float
      [prec(31) gather(E e) latex "{#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_/Float_)]

  declare _%Float_ : Float Float -> Float
      [prec(31) gather(E e) latex "{#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_%Float_)]

  declare _<=Float_ : Float Float -> Bool
      [prec(51) gather(E e) latex "{#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_<=Float_)]

  declare _<Float_ : Float Float -> Bool
      [prec(51) gather(E e) latex "{#1}\mathrel{<_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_<Float_)]

  declare _>=Float_ : Float Float -> Bool
      [prec(51) gather(E e) latex "{#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_>=Float_)]

  declare _>Float_ : Float Float -> Bool
      [prec(51) gather(E e) latex "{#1}\mathrel{>_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_>Float_)]

  declare _==Float_ : Float Float -> Bool 
      [latex "{#1}\mathrel{==_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_==Float_)]

  declare _=/=Float_ : Float Float -> Bool
      [latex "{#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2}"]
  define F1:Float =/=Float F2:Float => notBool(F1 ==Float F2)

  declare Int2Float : Int -> Float 
      [latex "{\\it{}Int2Float}" hook(#CONVERSION:int2Float)]

  declare Float2Int : Float -> Int
      [latex "{\\it{}Float2Int}" hook(#CONVERSION:float2Int)]


end module
