module BOOL-SYNTAX-HOOKS
  syntax Bool ::= #Bool
endmodule

module BOOL-HOOKS
  imports BOOL-SYNTAX-HOOKS
 

  rule B1:Bool =/=Bool B2:Bool => notBool(B1 ==Bool B2)

  syntax Bool ::= "notBool" Bool			[function, left, latex("\neg_{\scriptstyle\it Bool}{#1}")]
				> Bool "andBool" Bool		[function, left, latex("{#1}\wedge_{\scriptstyle\it Bool}{#2}")]
				> Bool "xorBool" Bool		[function, left]
				> Bool "orBool" Bool		[function, left, latex("{#1}\vee_{\scriptstyle\it Bool}{#2}")]
				> Bool "impliesBool" Bool	[function, left]
				> left:
				  Bool "==Bool" Bool		[function, left, hook(#BOOL:_==Bool_)]
				| Bool "=/=Bool" Bool		[function, left]

  rule true orBool B:Bool => true
  rule false orBool B:Bool => B 

  rule true andBool A:Bool => A:Bool
  rule false andBool A:Bool => false

  rule false xorBool A:Bool => A:Bool
  rule A:Bool xorBool A:Bool => false

  rule notBool true => false
  rule notBool false => true

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true


  syntax KLabel ::= "'#andBool" // People should not be using this

  rule '#andBool((true => .List{K}),, _)
  rule '#andBool(true) => true 
  rule '#andBool(false,, _) => false
endmodule
