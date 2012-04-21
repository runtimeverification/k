require bool
module K-EQUAL-HOOKS
  imports BOOL-HOOKS 

  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function]
  define #if true #then K:K #else _ #fi => K
  define #if false #then _ #else K:K #fi => K

  syntax Bool ::= K "==K" K           [function hook(#K-EQUAL:_==K_)]
  syntax Bool ::= K "=/=K" K           [function]
  define K1:K =/=K K2:K => notBool(K1 ==K K2)

  syntax Bool ::= List "<=List" List           [function]
  define ListItem(K:K) List1:List <=List ListItem(K) List2:List => List1 <=List List2
  define .List <=List List:List => true
  define ListItem(K:K) List1:List <=List List2:List => false
    when notBool (K in List2)
  syntax Bool ::= List "==List" List           [function]
  define List1:List ==List List2:List => (List1 <=List List2) andBool (List2 <=List List1)
  syntax Bool ::= List "=/=List" List           [function]
  define List1:List =/=List List2:List => notBool(List1 ==List List2)
  
  syntax Bool ::= Set "<=Set" Set    [function]
  define SetItem(K:K) Set1:Set <=Set SetItem(K) Set2:Set => Set1 <=Set Set2
  define .Set <=Set Set:Set => true
  define SetItem(K:K) Set1:Set <=Set Set2:Set => false
    when notBool (K in Set2)
  syntax Bool ::= Set "==Set" Set    [function]
  define Set1:Set ==Set Set2:Set => (Set1 <=Set Set2) andBool (Set2 <=Set Set1)
  syntax Bool ::= Set "=/=Set" Set   [function]
  define Set1:Set =/=Set Set2:Set => notBool(Set1 ==Set Set2)
  
  syntax Bool ::= Bag "<=Bag" Bag    [function]
  define BagItem(K:K) Bag1:Bag <=Bag BagItem(K) Bag2:Bag => Bag1 <=Bag Bag2
  define .Bag <=Bag Bag:Bag => true
  define BagItem(K:K) Bag1:Bag <=Bag Bag2:Bag => false
    when notBool (K in Bag2)
  syntax Bool ::= Bag "==Bag" Bag    [function]
  define Bag1:Bag ==Bag Bag2:Bag => (Bag1 <=Bag Bag2) andBool (Bag2 <=Bag Bag1)
  syntax Bool ::= Bag "=/=Bag" Bag   [function]
  define Bag1:Bag =/=Bag Bag2:Bag => notBool(Bag1 ==Bag Bag2)

  syntax Bool ::= List`{K`} "==List{K}" List`{K`}    [function]
  define LK1:List{K} ==List{K} LK2:List{K} => 'dummy(LK1) ==K 'dummy(LK2)
  syntax Bool ::= List`{K`} "=/=List{K}" List`{K`}   [function]
  define LK1:List{K} =/=List{K} LK2:List{K} => notBool(LK1 ==List{K} LK2)

  syntax Bool ::= KLabel "==KLabel" KLabel   [function]
  define '_==KLabel_(K1:K,,K2:K) => K1 ==K K2
  syntax Bool ::= KLabel "=/=KLabel" KLabel   [function]
  define '_=/=KLabel_(K1:K,,K2:K) => K1 =/=K K2
  
  syntax Bool ::= CellLabel "==CellLabel" CellLabel   [function]
  define '_==CellLabel_(K1:K,,K2:K) => K1 ==K K2
  syntax Bool ::= CellLabel "=/=CellLabel" CellLabel   [function]
  define '_=/=CellLabel_(K1:K,,K2:K) => K1 =/=K K2

end module
