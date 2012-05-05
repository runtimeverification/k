module BOOL-SYNTAX-HOOKS
  syntax Bool ::= #Bool
end module

module BOOL-HOOKS
  imports BOOL-SYNTAX-HOOKS
 
  syntax Bool ::= Bool "==Bool" Bool 
        [function hook(#BOOL:_==Bool_) latex "\builtinEqBool{{#1}}{{#2}}"]

  syntax Bool ::= Bool "=/=Bool" Bool
        [function latex "\builtinNeqBool{{#1}}{{#2}}"]
  define B1:Bool =/=Bool B2:Bool => notBool(B1 ==Bool B2)

  syntax Bool ::= Bool "andBool" Bool
        [function prec(55) gather(E e) latex "\builtinAnd{{#1}}{{#2}}"]
  syntax Bool ::= Bool "orBool" Bool  
        [function prec(59) gather(E e) latex "\builtinOr{{#1}}{{#2}}"]
  syntax Bool ::= Bool "xorBool" Bool
        [function prec(57) gather(E e) latex "\builtinXor{{#1}}{{#2}}"]
  syntax Bool ::= "notBool" Bool 
        [function prec(53) latex "\builtinNot{{#1}}"]
  syntax Bool ::= Bool "impliesBool" Bool
        [function prec(61) gather(e E) latex "\builtinImplies{{#1}}"]

  define true orBool B:Bool => true
  define false orBool B:Bool => B 

  define true andBool A:Bool => A:Bool
  define false andBool A:Bool => false

  define true xorBool A:Bool => notBool A:Bool
  define false xorBool A:Bool => A:Bool

  define notBool true => false
  define notBool false => true

  define true impliesBool B:Bool => B
  define false impliesBool _:Bool => true

  syntax Bool ::= K "orElseBool" K [function  prec(59) gather(E e)]
  define true orElseBool _ => true
  define false orElseBool K:K => K

  syntax Bool ::= K "andThenBool" K [function  prec(59) gather(E e)]
  define false andThenBool _ => false
  define true andThenBool K:K => K

  syntax KLabel ::= "'#andBool" // People should not be using this

  define '#andBool((true => .List{K}),, _)
  define '#andBool(true) => true 
  define '#andBool(false,, _) => false
end module
