mod SYMBOLIC-INT is extending PL-INT .
  op symNzNat_ : Nat -> NzNat .
  op symInt_ : Nat -> Int .
  eq 0 >=Int N:NzNat = false .
  eq 0 >Int N:NzNat = false .
  eq 0 >=Int -Int N:NzNat = true .
  eq 0 >Int -Int N:NzNat = true .
  eq N:NzNat >=Int 0 = true .
  eq N:NzNat >Int 0 = true .
  eq -Int N:NzNat >=Int 0 = false .
  eq -Int N:NzNat >Int 0 = false .
  eq 0 +Nat N:NzNat = N:NzNat .
  eq N:Nat +Int N':Nat = N:Nat +Nat N':Nat .
  eq N:Nat -Int N:Nat = 0 .
  eq (N:Nat +Nat N':Nat) -Int (N:Nat +Nat N'':Nat) = N':Nat -Int N'':Nat .
 ceq (N:Nat +Nat N':Nat) -Int N'':Nat = N:Nat +Nat N''':Nat
  if N''':Nat := N':Nat -Int N'':Nat .
  eq N:Nat <=Int N':Nat = N':Nat -Int N:Nat >=Int 0 .
  eq N:Nat <Int N':Nat = N':Nat -Int N:Nat >Int 0 .
---  eq symNzNat(N:Nat) -Int symNzNat(N':Nat) >=Int 0 = N:Nat -Int N':Nat >=Int 0 .

 ceq N:Nat >=Int N':Nat = true if N':Nat <=Int N:Nat .
 ceq N:Nat >=Int N':Nat = false if N':Nat <=Int N:Nat = false .
 ceq N:Nat >Int N':Nat = true if N':Nat <Int N:Nat .
 ceq N:Nat >Int N':Nat = false if N':Nat <Int N:Nat = false .
endm

kmod STRONG-MEMORY-SAFETY-SEMANTICS is including BASIC-KERNELC-SEMANTICS  + SYMBOLIC-INT
  rule initialLoc => symNzNat(0) [structural]
  rule increment(symNzNat(N1),N2) => symNzNat(sNat(N1)) [structural]
  
  rule <mem_> _ |-> (initial => symInt(N)) <_/mem> <next> symNzNat(N => sNat(N)) </next>[structural]
  rule <env_> X:Id |-> (initial => symInt(N)) <_/env> <next> symNzNat(N => sNat(N)) </next>[structural]

  rule N1:Nat..N2:Nat +Nat sNat(N:Nat) => N2+Nat N,,N1..N2+Nat N [structural]
endkm
