require seq

module REF imports SEQ
  configuration <k> .K </k>  
                <mem> .Map </mem> <nextLoc> 0 </nextLoc>
  
  syntax K ::= Nat
             | ref K [strict]
             | * K [strict]
             | K := K [strict(2)]

  context * HOLE := _
  rule <k> ref V:KResult => N:Nat ...</k> 
       <mem>... . => N |-> V ...</mem> <nextLoc> N => N +Int 1 </nextLoc> 
  rule <k> * N => V ...</k> <mem>... N |-> V ...</mem> [transition]
  rule <k> * N := V => skip ...</k> <mem>... N |-> (_ => V) ...</mem> [transition]
end module
