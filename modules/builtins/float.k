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


end module
