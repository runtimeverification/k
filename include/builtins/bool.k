// Copyright (c) 2012-2014 K Team. All Rights Reserved.
module BOOL-SYNTAX-HOOKS
  imports #BOOL-INTERFACE

  syntax #Bool ::= "true"
  syntax #Bool ::= "false"
  syntax Bool ::= #Bool
endmodule

module BOOL-HOOKS
  imports BOOL-SYNTAX-HOOKS

  syntax Bool ::= "notBool" Bool          [function, smtlib(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(#BOOL:notBool_)]
                > Bool "andBool" Bool     [function, left, smtlib(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_andBool_)]
                | Bool "andThenBool" Bool [function, left, smtlib(and), boolOperation]
                > Bool "xorBool" Bool      [function, left, smtlib(xor), boolOperation, hook(#BOOL:_xorBool_)]
                > Bool "orBool" Bool      [function, left, smtlib(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_orBool_)]
                | Bool "orElseBool" Bool  [function, left, smtlib(or), boolOperation]
                > Bool "impliesBool" Bool [function, left, smtlib(=>), boolOperation, hook(#BOOL:_impliesBool_)]
                > left:
                  Bool "==Bool" Bool      [function, left, smtlib(=), hook(#BOOL:_==Bool_)]
                | Bool "=/=Bool" Bool      [function, left, smtlib(distinct), hook(#BOOL:_=/=Bool_)]

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
  syntax KLabel ::= "'#andBool" [predicate]
  rule '#andBool(_,, (true => .KList),, _) [function, anywhere, nojava]
  rule '#andBool(K:K) => K [anywhere]
  rule '#andBool(.KList) => true  [function, anywhere]
  rule '#andBool(_,, false,, _) => false [function, anywhere, nojava]
endmodule
