// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "bool.k"
require "int.k"
module FLOAT-SYNTAX-HOOKS
  imports #FLOAT-INTERFACE
  syntax #Float ::= Token{[\+\-]?[0-9]+"."[0-9]+([eE][\+\-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?}
                 [regex("([\\+-]?\\d(\\.\\d*)?|\\.\\d+)([eE][\\+-]?(\\d(\\.\\d*)?|\\.\\d+))?([fFdD]|([pP]\\d+[xX]\\d+))?")]
  syntax #Float ::= Token{[\+\-]?"Infinity"([fFdD]|([pP][0-9]+[xX][0-9]+))?}
                 [regex("[\\+-]?Infinity([fFdD]|([pP]\\d+[xX]\\d+))?")]
  syntax #Float ::= Token{"NaN"([fFdD]|([pP][0-9]+[xX][0-9]+))?}
                 [regex("NaN([fFdD]|([pP]\\d+[xX]\\d+))?")]
  //TODO(radumereuta): this needs to be made more general to reject NaNp24x8,
  //etc, once we switch to the new parser
  syntax #Float ::= "NaN" | "Infinity"
  syntax Float ::= #Float
endmodule

module FLOAT-HOOKS
  imports FLOAT-SYNTAX-HOOKS
  imports BOOL-HOOKS
  imports INT-HOOKS
  imports K

  syntax Int ::= precisionFloat(Float) [function, hook(#FLOAT:precision)]
               | exponentFloat(Float) [function, hook(#FLOAT:exponent)]
               | exponentBitsFloat(Float) [function, hook(#FLOAT:exponentBits)]

  syntax Bool ::= signFloat(Float) [function, hook(#FLOAT:sign)]
  syntax MInt ::= significandFloat(Float) [function, hook(#FLOAT:significand)]

  syntax Float ::= "--Float" Float          [function, hook(#FLOAT:neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(#FLOAT:pow)]
                 > left:
                   Float "*Float" Float        [function, left, latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:mul)]
                 | Float "/Float" Float        [function, left, latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:div)]
                 | Float "%Float" Float        [function, left, latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:rem)]
                 > left:
                   Float "+Float" Float        [function, left, latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:add)]
                 | Float "-Float" Float        [function, left, latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:sub)]

  syntax Float ::= rootFloat(Float, Int) [function, hook(#FLOAT:root)]
                 | absFloat(Float) [function, hook(#FLOAT:abs)]
                 | roundFloat(Float, Int, Int) [function, hook(#FLOAT:round)]
                 | floorFloat(Float) [function, hook(#FLOAT:floor)]
                 | ceilFloat(Float) [function, hook(#FLOAT:ceil)]
                 | expFloat(Float) [function, hook(#FLOAT:exp)]
                 | logFloat(Float) [function, hook(#FLOAT:log)]
                 | sinFloat(Float) [function, hook(#FLOAT:sin)]
                 | cosFloat(Float) [function, hook(#FLOAT:cos)]
                 | tanFloat(Float) [function, hook(#FLOAT:tan)]
                 | asinFloat(Float) [function, hook(#FLOAT:asin)]
                 | acosFloat(Float) [function, hook(#FLOAT:acos)]
                 | atanFloat(Float) [function, hook(#FLOAT:atan)]
                 | atan2Float(Float, Float) [function, hook(#FLOAT:atan2)]
                 | maxFloat(Float, Float) [function, hook(#FLOAT:max)]
                 | minFloat(Float, Float) [function, hook(#FLOAT:min)]

  syntax Bool ::= left:
                    Float "<=Float" Float        [function, left, latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:le)]
                | Float "<Float" Float        [function, left, latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:lt)]
                | Float ">=Float" Float        [function, left, latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:ge)]
                | Float ">Float" Float        [function, left, latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:gt)]
                | Float "==Float" Float        [function, left, latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:eq)]
                | Float "=/=Float" Float    [function, left, latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool(F1 ==Float F2)

  syntax Float ::= Int2Float(Int, Int, Int)    [function, klabel(Int2Float), latex({\\it{}Int2Float}), hook(#CONVERSION:int2Float)]
  syntax Int ::= Float2Int(Float)    [function, klabel(Float2Int), latex({\\it{}Float2Int}), hook(#CONVERSION:float2Int)]


endmodule
