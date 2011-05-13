kmod PI-IO-SEMANTICS is including PI-IO-SYNTAX + PI-SEMANTICS 
  configuration <T> <sum*> <k*> .K </k*> </sum*> <nextId> 0 </nextId> 
                <out> .List </out> </T>
  rule (<sum_> <k> send X:Id on print . P:Proc </k> <_/sum> => <sum> <k> P </k> </sum>)
     <out_>. => ListItem(X)</out>
  
  op input_ : List{K} -> Proc [latex "input({#1})"]
  macro input(.List{K}) = ()
  macro input(X,,L:List{K}) = send X on read . input(L)
endkm
