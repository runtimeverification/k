kmod PI-ALL-SEMANTICS is including PI-SYNTAX + SUBSTITUTION
  syntax K ::= Action | Proc
             
  rule <k> P + Q => P </k> => <k> P </k> <k> Q </k>
  
  rule <sum> <k> P || Q:Proc </k> </sum>  => <sum> <k>P</k> </sum>  <sum> <k>Q</k> </sum>   
  rule [comm] : (<sum_> <k> send X:Id on C:Id . P:Proc </k>  <_/sum> => <sum> <k> P </k> </sum>)
       (<sum_> <k> receive Y:Id on C . Q </k> <_/sum> =>
       <sum> <k> Q[X/Y] </k> </sum>)

  rule <k>()</k> => . [structural]
  rule <sum> .Bag </sum> => . [structural]
  
  rule [!comm] : <sum> <k> (send X on C . P => P) </k> (_ => .)
                 </sum>
                 <sum> <k> replicate  receive Y on C . Q </k> (_ => .) </sum> (. => <sum> <k> Q[X/Y] </k> </sum>)


  syntax K ::= top Bag
  configuration <T> <sum*> <k*> .K </k*> </sum*> </T>
             
  
  rule '_._(A:Action,, ((P:Proc || Q:Proc) => top(<T> <sum> <k> P </k> </sum> <sum> <k> Q </k> </sum> </T>))) [structural]

  rule <sum> <k> top(<T> B:Bag </T>) </k> </sum> => B [structural]


  rule [extrusion] : ('top_ => addNu(X))(wbag(<T_> <sum_> <k>new X . P => P</k> <_/sum> <_/T>))
  
  syntax KLabel ::= addNu( K )
  rule addNu(X)(wbag(B)) => new X . top(B) [structural]
endkm
