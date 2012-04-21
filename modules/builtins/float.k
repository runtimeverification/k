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

  syntax Float ::= Float "+Float" Float
      [function prec(33) gather(E e) latex "{#1}\mathrel{+_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_+Float_)]

  syntax Float ::= Float "-Float" Float
      [function prec(33) gather(E e) latex "{#1}\mathrel{-_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_-Float_)]

  syntax Float ::= Float "*Float" Float
      [function prec(31) gather(E e) latex "{#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_*Float_)]

  syntax Float ::= Float "/Float" Float
      [function prec(31) gather(E e) latex "{#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_/Float_)]

  syntax Float ::= Float "%Float" Float
      [function prec(31) gather(E e) latex "{#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_%Float_)]

  syntax Bool ::= Float "<=Float" Float
      [function prec(51) gather(E e) latex "{#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_<=Float_)]

  syntax Bool ::= Float "<Float" Float
      [function prec(51) gather(E e) latex "{#1}\mathrel{<_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_<Float_)]

  syntax Bool ::= Float ">=Float" Float
      [function prec(51) gather(E e) latex "{#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_>=Float_)]

  syntax Bool ::= Float ">Float" Float
      [function prec(51) gather(E e) latex "{#1}\mathrel{>_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_>Float_)]

  syntax Bool ::= Float "==Float" Float
      [function latex "{#1}\mathrel{==_{\scriptstyle\it Float}}{#2}"
       hook(#FLOAT:_==Float_)]

  syntax Bool ::= Float "=/=Float" Float
      [function latex "{#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2}"]
  define F1:Float =/=Float F2:Float => notBool(F1 ==Float F2)

  syntax Float ::= "Int2Float" "(" Int ")"
      [function klabel(Int2Float) latex "{\\it{}Int2Float}" hook(#CONVERSION:int2Float)]

  syntax Int ::= "Float2Int" "(" Float ")"
      [function klabel(Float2Int) latex "{\\it{}Float2Int}" hook(#CONVERSION:float2Int)]

  syntax Float ::= "sqrtFloat" "(" Float ")" [function hook(#FLOAT:sqrtFloat)]
  syntax Float ::= "logFloat" "(" Float ")" [function hook(#FLOAT:logFloat)]
  syntax Float ::= "expFloat" "(" Float ")" [function hook(#FLOAT:expFloat)]
  syntax Float ::= "atanFloat" "(" Float ")" [function hook(#FLOAT:atanFloat)]
  syntax Float ::= "acosFloat" "(" Float ")" [function hook(#FLOAT:acosFloat)]
  syntax Float ::= "asinFloat" "(" Float ")" [function hook(#FLOAT:asinFloat)]
  syntax Float ::= "tanFloat" "(" Float ")" [function hook(#FLOAT:tanFloat)]
  syntax Float ::= "cosFloat" "(" Float ")" [function hook(#FLOAT:cosFloat)]
  syntax Float ::= "sinFloat" "(" Float ")" [function hook(#FLOAT:sinFloat)]
  syntax Float ::= "atan2Float" "(" Float "," Float ")" [function hook(#FLOAT:atanFloat)]
  syntax Float ::= "floorFloat" "(" Float ")" [function hook(#FLOAT:floorFloat)]

end module
