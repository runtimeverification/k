require seq

kmod IO is including SEQ + PL-INT
  configuration <k> .K </k>  
                <in> .List </in> <out> .List </out>
  syntax K ::= Int
             | read
             | print K [strict]
  
   rule <k>read => I:Int<_/k> <in>ListItem(I) => .<_/in>
   rule <k>print V:KResult => skip <_/k> <out_>. => ListItem(V)</out>
endkm
