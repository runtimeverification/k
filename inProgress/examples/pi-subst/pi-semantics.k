kmod PI-SEMANTICS is including PI-SYNTAX + SUBSTITUTION + PL-COUNTER
  syntax K ::= Action | Proc
             
  configuration <T> <sum*> <k*> .K </k*> </sum*> </T>

---(             
  syntax K ::= nu K [latex "\nu{#1}"]
             | apply K to received ( K )  [latex "{#2}?{#1}"]
 
  macro new X:Id.P:Proc = nu([X]P)
  macro receive X on C . P = apply([X]P) to received(C)
---)

  rule <k> P:Proc + Q </k> => <k> P </k> <k> Q </k>
  
  rule <sum> <k> P || Q:Proc  </k> </sum>  => <sum> <k>P</k> </sum>  <sum> <k>Q</k> </sum>  
  rule [comm] : (<sum_> <k> send X:Id on C:Id . P </k>  <_/sum> => <sum> <k> P </k> </sum>)
       (<sum_> <k> receive Y:Id on C . Q </k> <_/sum> =>
       <sum> <k> Q[X/Y] </k> </sum>)

  rule <k>()</k> => . [structural]
  rule <sum> .Bag </sum> => . [structural]
  
  rule [nu] : <k>new X . P => P[id kcounter / X]</k>
  
  rule [!comm] : (<sum_> <k> send X on C . P </k> 
                 <_/sum> => <sum> <k> P </k> </sum>)
                 <k> replicate receive Y on C . Q </k>  (. => <sum> <k> Q[X/Y] </k> </sum>)
endkm
