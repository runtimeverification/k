

kmod PRIMES is
  configuration <primes> .Bag </primes>
  syntax K ::= #NzNat
  rule <primes>... BagItem(N:#NzNat) (BagItem(M:#NzNat)=>.) ...</primes>
    when N dividesNat M
endkm

kmod RUN is including PRIMES
  syntax Bag ::= run ( #NzNat )
  syntax Bag ::= 2 .. #Nat
  macro 2..sNat(M:#Nat) = if (M ==Bool 0) then . else 2..M BagItem(sNat(M)) fi
  macro run(N:#NzNat) = <primes>2..N</primes>
endkm
