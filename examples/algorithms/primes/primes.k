

kmod PRIMES is
  configuration <primes> .Bag </primes>
  rule <primes>... BagItem(N:Nat) (BagItem(M:Nat)=>.) ...</primes>
    when N dividesInt M
endkm

kmod RUN is including PRIMES
  syntax Bag ::= run ( Nat )
  syntax Bag ::= 2 .. Nat
  define 2..M:Nat => . when M <Int 2
  define 2..M:Nat => 2..(M -Int 1) BagItem(M) when M >=Int 2
  define run(N:Nat) => <primes>2..N</primes>
endkm
