require bool
module K-EQUAL-HOOKS
  imports BOOL-HOOKS 
---  declare _==K_ : K K -> Bool
  syntax Bool ::= K "==K" K           [function hook(#K-EQUAL:_==K_)]
---  declare _=/=K_ : K K -> Bool
  syntax Bool ::= K "=/=K" K          [function]
  define K1:K =/=K K2:K => notBool(K1 ==K K2)

---  declare #if_#then_#else_#fi : Bool K K -> K 
  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function]
  define #if true #then K:K #else _ #fi => K
  define #if false #then _ #else K:K #fi => K

---  declare _<=Set_ : Set Set -> Bool
  syntax Bool ::= Set "<=Set" Set    [function]
  define SetItem(K:K) Set1:Set <=Set SetItem(K) Set2:Set => Set1 <=Set Set2
  define .Set <=Set Set:Set => true
  define SetItem(K:K) Set1:Set <=Set Set2:Set => false
  when notBool (K in Set2)

---  declare _==Set_ : Set Set -> Bool
  syntax Bool ::= Set "==Set" Set    [function]
  define Set1:Set ==Set Set2:Set => (Set1 <=Set Set2) andBool (Set2 <=Set Set1)

---  declare _=/=Set_ : Set Set -> Bool
  syntax Bool ::= Set "=/=Set" Set   [function]
  define Set1:Set =/=Set Set2:Set => notBool(Set1 ==Set Set2)

---  declare  _==List{K}_ : List`{K`} List`{K`} -> Bool
  syntax Bool ::= List`{K`} "==List{K}" List`{K`}    [function]
  define LK1:List{K} ==List{K} LK2:List{K} => 'dummy(LK1) ==K 'dummy(LK2)

---  declare  _=/=List{K}_ : List`{K`} List`{K`} -> Bool
  syntax Bool ::= List`{K`} "=/=List{K}" List`{K`}   [function]
  define LK1:List{K} =/=List{K} LK2:List{K}  => notBool(LK1 ==List{K} LK2)

---  declare _==KLabel_ : KLabel KLabel -> Bool
  syntax Bool ::= KLabel "==KLabel" KLabel   [function]
  define '_==KLabel_(K1:K,,K2:K) => K1 ==K K2

end module
