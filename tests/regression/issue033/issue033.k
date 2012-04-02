

module ISSUE033A
  syntax KResult ::= Type
  syntax Type ::= arrayType ( Type , Nat )
                | bool
  syntax K ::= testa ( Map , Type , Nat )  | Bool

 define testa(Cache:Map, T:Type, N:Nat) => true
   when notBool($hasMapping(Cache:Map, arrayType(T:Type, N:Nat)))
end module

module ISSUE033B is 
 syntax K ::= kpair ( K , List )
            | case ( Nat ,  BaseValue ) 
            | Nat | BaseValue | Id
            | testb ( Map , Nat , BaseValue , Id )
 syntax BaseValue ::= Bool
 syntax Id ::= a
 define testb(LM:Map,SN:Nat,V:BaseValue,F:Id) => true
  when notBool $hasMapping(LM:Map, 
            kpair(F:Id, List(case(SN:Nat, V:BaseValue))))

end module

module ISSUE033 imports ISSUE033B + ISSUE033A
  syntax K ::= test 
  macro test = 'both(testa(.,bool,0),,testb(.,0,false,a)) 
  define 'both(true,,true) => true
end module
