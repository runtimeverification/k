module BOOL-SYNTAX-HOOKS
  syntax Bool ::= #Bool
end module

module BOOL-HOOKS
  imports BOOL-SYNTAX-HOOKS
 
  syntax Bool ::= Bool "==Bool" Bool   [function hook(#BOOL:_==Bool_)]

  syntax Bool ::= Bool "=/=Bool" Bool   [function]
  define B1:Bool =/=Bool B2:Bool => notBool(B1 ==Bool B2)

  syntax Bool ::= Bool "andBool" Bool
        [function prec(55) gather(E e) latex "{#1}\wedge_{\scriptstyle\it Bool}{#2}"]
  syntax Bool ::= Bool "orBool" Bool  
        [function prec(59) gather(E e) latex "{#1}\vee_{\scriptstyle\it Bool}{#2}"]
  syntax Bool ::= Bool "xorBool" Bool 
        [function prec(57) gather(E e)]
  syntax Bool ::= "notBool" Bool 
        [function prec(53) latex "\neg_{\scriptstyle\it Bool}{#1}"]
  syntax Bool ::= Bool "impliesBool" Bool
        [function prec(61) gather(e E)]

  define true orBool B:Bool => true
  define false orBool B:Bool => B 

  define true andBool A:Bool => A:Bool
  define false andBool A:Bool => false

  define false xorBool A:Bool => A:Bool
  define A:Bool xorBool A:Bool => false

  define notBool true => false
  define notBool false => true

  define true impliesBool B:Bool => B
  define false impliesBool _:Bool => true


  syntax KLabel ::= "'#andBool" // People should not be using this

  define '#andBool((true => .List{K}),, _)
  define '#andBool(true) => true 
  define '#andBool(false,, _) => false
end module
