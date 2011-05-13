kmod PI-ALL-SEMANTICS is including PI-SYNTAX + SUBSTITUTION  + PL-COUNTER + K-WRAPPERS
  syntax K ::= Action | Proc
             
  syntax K ::= nu K [latex "\nu{#1}"]
             | apply K to received ( K )  [latex "{#2}?{#1}"]
 
  macro new X:Id.P:Proc = nu([X]P)
  macro receive X on C . P = apply([X]P) to received(C)


  rule <k> P + Q => P </k> (. => <k> Q </k>)
  
  rule <sum_> <k> P || Q:Proc => P </k> <_/sum>  (. => <sum> <k>Q</k> </sum> )  
  rule [comm] : (<sum_> <k> send X on C:Id . P </k>  <_/sum> => <sum> <k> P </k> </sum>)
       (<sum_> <k> apply([Y:Id]Q) to received(C) </k> <_/sum> =>
       <sum> <k> Q[X/Y] </k> </sum>)

  rule <k>()</k> => . [structural]
  rule <sum> .Bag </sum> => . [structural]
  
  rule [!comm] : (<sum_> <k> send X on C . P </k> 
                 <_/sum> => <sum> <k> P </k> </sum>)
                 <k> 'replicate_(apply ([Y]Q) to received(C)) </k>  (. => <sum> <k> Q[X/Y] </k> </sum>)


  syntax K ::= top Bag
  configuration <T> <sum*> <k*> .K </k*> </sum*> <nextId> kcounter </nextId> </T>
             
  
  rule '_._(A:Action,, ((P:Proc || Q:Proc) => top(<T> <sum> <k> P </k> </sum> <sum> <k> Q </k> </sum> <nextId> kcounter *Nat 1000 </nextId> </T>))) [structural]

  rule (<sum> <k> top(<T> B:Bag <nextId> _:Nat </nextId> </T>) </k> </sum> => B)
        <nextId> _ => kcounter *Nat 1000 </nextId> [structural]


  rule [nu] : ('top_ => addNu(id N))(wbag(<T_> <sum_> <k>nu([X]P) => P[id N / X]</k> <_/sum> <nextId>N => sNat N:Nat</nextId> <_/T>))
  
  syntax KLabel ::= addNu( K )
  rule addNu(id N)(wbag(B)) => nu([id N]top(B)) [structural]
endkm
