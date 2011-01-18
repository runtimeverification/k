in ../../k-prelude

kmod ISSUE033A is including K + PL-NAT + PL-ID
  syntax KResult ::= Type
  syntax Type ::= arrayType ( Type , Nat )
                | bool
  syntax K ::= testa ( Map , Type , Nat )  | Bool

 rule testa(Cache:Map, T:Type, N:Nat) => true
   if notBool($hasMapping(Cache:Map, arrayType(T:Type, N:Nat)))
endkm

kmod ISSUE033B is including K + PL-NAT + PL-ID
 syntax K ::= kpair ( K , List )
            | case ( Nat ,  BaseValue ) 
            | Nat | BaseValue | Id
            | testb ( Map , Nat , BaseValue , Id )
 syntax BaseValue ::= Bool
 syntax Id ::= a
 rule testb(LM:Map,SN:Nat,V:BaseValue,F:Id) => true
  if notBool $hasMapping(LM:Map, kpair(F:Id, List(case(SN:Nat, V:BaseValue))))
endkm

kmod ISSUE033 is including ISSUE033B + ISSUE033A
  syntax K ::= test 
  macro test = 'both(testa(.,bool,0),,testb(.,0,true,a)) 
  rule 'both(true,,true) => true
endkm
