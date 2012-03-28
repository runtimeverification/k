require bool
module K-EQUAL-HOOKS
  imports BOOL-HOOKS 
  declare _==K_ : K K -> Bool [hook(#K-EQUAL:_==K_)]
  declare _=/=K_ : K K -> Bool
  define K1:K =/=K K2:K => notBool(K1 ==K K2)

  declare #if_#then_#else_#fi : Bool K K -> K 
  define #if true #then K:K #else _ #fi => K
  define #if false #then _ #else K:K #fi => K
end module
