require kernelc
mod #SYMBOLIC-INT is extending #INT .
  op symNzNat_ : #Nat -> #NzNat .
  op symInt_ : #Nat -> #Int .
  eq 0 >=Int N:#NzNat = false .
  eq 0 >Int N:#NzNat = false .
  eq 0 >=Int -Int N:#NzNat = true .
  eq 0 >Int -Int N:#NzNat = true .
  eq N:#NzNat >=Int 0 = true .
  eq N:#NzNat >Int 0 = true .
  eq -Int N:#NzNat >=Int 0 = false .
  eq -Int N:#NzNat >Int 0 = false .
  eq 0 +Nat N:#NzNat = N:#NzNat .
  eq N:#Nat +Int N':#Nat = N:#Nat +Nat N':#Nat .
  eq N:#Nat -Int N:#Nat = 0 .
  eq (N:#Nat +Nat N':#Nat) -Int (N:#Nat +Nat N'':#Nat) = N':#Nat -Int N'':#Nat .
 ceq (N:#Nat +Nat N':#Nat) -Int N'':#Nat = N:#Nat +Nat N''':#Nat
  if N''':#Nat := N':#Nat -Int N'':#Nat .
  eq N:#Nat <=Int N':#Nat = N':#Nat -Int N:#Nat >=Int 0 .
  eq N:#Nat <Int N':#Nat = N':#Nat -Int N:#Nat >Int 0 .
---  eq symNzNat(N:#Nat) -Int symNzNat(N':#Nat) >=Int 0 = N:#Nat -Int N':#Nat >=Int 0 .

 ceq N:#Nat >=Int N':#Nat = true if N':#Nat <=Int N:#Nat .
 ceq N:#Nat >=Int N':#Nat = false if N':#Nat <=Int N:#Nat = false .
 ceq N:#Nat >Int N':#Nat = true if N':#Nat <Int N:#Nat .
 ceq N:#Nat >Int N':#Nat = false if N':#Nat <Int N:#Nat = false .
endm

kmod SAFE-MALLOC-SEMANTICS is including KERNELC-SEMANTICS + #SYMBOLIC-INT

  rule <k> (int *)malloc(N:#Nat*sizeof(int)) => N':#Nat <_/k>
       <ptr_> . => symNzNat(N') |-> N <_/ptr>    <br/>
       <mem_> . => N'..N' +Nat N |-> undef <_/mem> 
       <next> N' => N' +Int N </next>  
   [large]

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> 
  
endkm

