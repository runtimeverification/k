kmod PI-ALL-SEMANTICS is including PI-SEMANTICS + PL-COUNTER
  syntax K ::= top Bag
  configuration <T> <sum*> <k*> .K </k*> </sum*> <nextId> kcounter </nextId> </T>
             
  
  rule '_._(A:Action,, ((P:Proc || Q:Proc) => top(<T> <sum> <k> P </k> </sum> <sum> <k> Q </k> </sum> <nextId> kcounter *Nat 1000 </nextId> </T>))) [structural]

  rule (<sum> <k> top(<T> B:Bag <nextId> _:Nat </nextId> </T>) </k> </sum> => B)
        <nextId> _ => kcounter *Nat 1000 </nextId> [structural]
  
endkm
