module BOOL-SYNTAX-HOOKS
  imports #BOOL-INTERFACE
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

  rule true orBool B:Bool => true [function, anywhere]
  rule false orBool B:Bool => B [function, anywhere]

  rule true andBool A:Bool => A:Bool [function, anywhere]
  rule false andBool A:Bool => false [function, anywhere]

  rule false xorBool A:Bool => A:Bool [function, anywhere]
  rule A:Bool xorBool A:Bool => false [function, anywhere]

  rule notBool true => false [function, anywhere]
  rule notBool false => true [function, anywhere]

  rule true impliesBool B:Bool => B [function, anywhere]
  rule false impliesBool _:Bool => true [function, anywhere]


  //syntax KLabel ::= "'#andBool" // People should not be using this

  rule '#andBool((true => .List{K}),, _) [function, anywhere]
  rule '#andBool(true) => true  [function, anywhere]
  rule '#andBool(false,, _) => false [function, anywhere]
endmodule
