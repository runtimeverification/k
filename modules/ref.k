require seq

module REF imports SEQ
  configuration <k> .K </k>  
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
  
  syntax K ::= #Nat
             | ref K [strict]
             | * K [strict]
             | K := K [strict(2)]

  context * [HOLE] := _
  rule <k> ref V:KResult => N:#Nat <_/k> 
       <mem_> . => N |-> V <_/mem> <nextLoc> N => sNat N </nextLoc> 
  rule <k> * N => V <_/k> <mem_> N |-> V <_/mem> [transition]
  rule <k> * N := V => skip <_/k> <mem_> N |-> (_ => V) <_/mem> [transition]
end module
