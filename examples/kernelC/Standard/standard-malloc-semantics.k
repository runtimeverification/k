
kmod STANDARD-MALLOC-SEMANTICS is including BASIC-KERNELC-SEMANTICS  
  configuration <T> <k> .K </k> <mem> .Map </mem> <ptr> .Map </ptr>
                    <next> 1 </next> <env> .Map </env> <out> "" </out> </T>
  context *[HOLE]=_
  
  rule <k> *N:Nat => V:Val <_/k> <mem_> N |-> V <_/mem>
  rule <k> *N=V => V <_/k> <mem_> N |-> (_ => V) <_/mem>
  rule <k> malloc(N) => N':Nat <_/k>  <ptr_> . => N' |-> N <_/ptr> 
       <mem_> . => N'..N' +Nat N |-> 0 <_/mem> <next> N' => N' +Nat N </next>

  rule <k> free(N) => void <_/k> <ptr_> N |-> N' => . <_/ptr>
       <mem> Mem:Map => Mem[undef/N..N'+Nat N] </mem> 

--- auxiliary functions
  syntax List{K} ::= Nat .. Nat
  rule N1:Nat..N1 => .List{K} [structural]
  rule N1..N2:Nat => N1,,sNat N1..N2 [structural]
endkm
