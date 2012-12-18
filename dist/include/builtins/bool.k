module BOOL-SYNTAX-HOOKS
  imports #BOOL-INTERFACE

  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  syntax Bool ::= #Bool
endmodule

module BOOL-HOOKS
  imports BOOL-SYNTAX-HOOKS
 
  syntax Bool ::= "notBool" Bool  [function, left, smtlib(not), latex(\neg_{\scriptstyle\it Bool}{#1})]
				> Bool "andBool" Bool     [function, left, smtlib(and), latex({#1}\wedge_{\scriptstyle\it Bool}{#2})]
				| Bool "andThenBool" Bool [function, left, smtlib(and)]
				> Bool "xorBool" Bool		  [function, left, smtlib(xor)]
				> Bool "orBool" Bool		  [function, left, smtlib(or), latex({#1}\vee_{\scriptstyle\it Bool}{#2})]
				| Bool "orElseBool" Bool  [function, left, smtlib(or)]
				> Bool "impliesBool" Bool	[function, left, smtlib(=>)]
				> left:
				  Bool "==Bool" Bool		[function, left, smtlib(=), hook(#BOOL:_==Bool_)]
				| Bool "=/=Bool" Bool		[function, left, smtlib(distinct)]

  rule notBool true => false
  rule notBool false => true

  rule true andBool B:Bool => B:Bool
  rule B:Bool andBool true => B:Bool
  rule false andBool _:Bool => false
  rule _:Bool andBool false => false

  rule true andThenBool K:K => K
  rule K:K andThenBool true => K
  rule false andThenBool _ => false
  rule _ andThenBool false => false

  rule false xorBool B:Bool => B:Bool
  rule B:Bool xorBool false => B:Bool
  rule B:Bool xorBool B:Bool => false
  rule B1:Bool xorBool B2:Bool => notBool (B1 ==Bool B2)

  rule true orBool _:Bool => true
  rule _:Bool orBool true => true
  rule false orBool B:Bool => B
  rule B:Bool orBool false => B

  rule true orElseBool _ => true
  rule _ orElseBool true => true
  rule false orElseBool K:K => K
  rule K:K orElseBool false => K

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true
  rule _:Bool impliesBool true => true
  rule B:Bool impliesBool false => notBool B
  
  rule B1:Bool =/=Bool B2:Bool => notBool(B1 ==Bool B2)

  // Andrei S: why are the rules below needed?
  // Traian S.:  They are needed in the generated code, as we allow 
  // '#andBool to take multiple parameters.
  rule '#andBool((true => .List{K}),, _) [function, anywhere]
  rule '#andBool(.List{K}) => true  [function, anywhere]
  rule '#andBool(false,, _) => false [function, anywhere]
endmodule

