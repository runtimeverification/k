// Copyright (C) 2014 K Team. All Rights Reserved.
require "bool.k"
require "int.k"
module FLOAT-SYNTAX-HOOKS
  imports #FLOAT-INTERFACE
  syntax #Float
  syntax Float ::= #Float
endmodule

module FLOAT-HOOKS
  imports FLOAT-SYNTAX-HOOKS
  imports BOOL-HOOKS
  imports INT-HOOKS
  imports K

  syntax Float ::= "--Float" Float              [function, hook(#FLOAT:-Float_)]
				 > Float "^Float" Float		[function, left, latex({#1}^{#2}), hook(#FLOAT:_^Float_)]
                 > left:
				   Float "*Float" Float		[function, left, latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_*Float_)]
				 | Float "/Float" Float		[function, left, latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_/Float_)]
				 | Float "%Float" Float		[function, left, latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_%Float_)]
				 > left:
				   Float "+Float" Float		[function, left, latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_+Float_)]
				 | Float "-Float" Float		[function, left, latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_-Float_)]

  syntax Bool ::= left:
  				  Float "<=Float" Float		[function, left, latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_<=Float_)]
				| Float "<Float" Float		[function, left, latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_<Float_)]
				| Float ">=Float" Float		[function, left, latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_>=Float_)]
				| Float ">Float" Float		[function, left, latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_>Float_)]
				| Float "==Float" Float		[function, left, latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:_==Float_)]
				| Float "=/=Float" Float	[function, left, latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]
				> Float "<=Float" Float "<=Float" Float
	[function, latex({#2}\in[{#1},{#3}]), hook(#FLOAT:_<=Float_<=Float_)]


  rule F1:Float =/=Float F2:Float => notBool(F1 ==Float F2)

  syntax Float ::= "Int2Float" "(" Int ")"	[function, klabel(Int2Float), latex({\\it{}Int2Float}), hook(#CONVERSION:int2Float)]
  syntax Int ::= "Float2Int" "(" Float ")"	[function, klabel(Float2Int), latex({\\it{}Float2Int}), hook(#CONVERSION:float2Int)]


endmodule
