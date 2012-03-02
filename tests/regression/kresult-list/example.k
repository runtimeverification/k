module KRESULT-LIST
  syntax KResult ::= #Int | #Bool

  op bitSizeofList : List{KResult} -> K
  op bitSizeofList-aux : K #Nat List{KResult} -> K [metadata "strict=(1)"]
  define bitSizeofList(L:List{KResult}) => bitSizeofList-aux(.K, 0, L:List{KResult}) [structural]
  define bitSizeofList-aux(K:K, (N:#Nat => N +Nat 1), (R:KResult,,L:List{KResult} => L))
  define bitSizeofList-aux(K:K, N:#Nat, .List{K}) => N 

  syntax K ::= test

  define test => bitSizeofList((3,,5,,true,,7,,false)) [structural]
end module
