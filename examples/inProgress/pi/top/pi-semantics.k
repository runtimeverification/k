kmod PI-SEMANTICS is including PI-SYNTAX + SUBSTITUTION 
  syntax K ::= Action | Proc
             
  configuration <T> <sum*> <k*> .K </k*> </sum*> <nextId> 0 </nextId> </T>
             
  syntax K ::= nu K [latex "\nu{#1}"]
             | apply K to received ( K )  [latex "{#2}?{#1}"]

  macro new X:Id.P:Proc = nu([X]P)
  macro receive X on C . P = apply([X]P) to received(C)


  rule <k> P + Q => P </k> (. => <k> Q </k>)
  
  rule <sum_> <k> P || Q:Proc => P </k> <_/sum>  (. => <sum> <k>Q</k> </sum> )  
  rule [comm] : (<sum_> <k> send X on C:Id . P </k>  <_/sum> => <sum> <k> P </k> </sum>)
       (<sum_> <k> apply([Y:Id]Q) to received(C) </k> <_/sum> =>
       <sum> <k> Q[X/Y] </k> </sum>)
  rule tau . P => P [structural]

  rule <k>()</k> => . [structural]
  rule <sum> .Bag </sum> => . [structural]
  
  rule [nu] : <k>nu([X]P) => P[id N / X]</k> <nextId>N => sNat N:Nat</nextId>
  
  rule [!comm] : (<sum_> <k> send X on C . P </k> 
                 <_/sum> => <sum> <k> P </k> </sum>)
                 <k> 'replicate_(apply ([Y]Q) to received(C)) </k>  (. => <sum> <k> Q[X/Y] </k> </sum>)
endkm
