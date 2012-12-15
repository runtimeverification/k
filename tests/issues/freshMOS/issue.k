module ISSUE
  syntax K ::= function(K,K) 
             | "test"
             | "bad"
             | "good"

   configuration <k> $PGM:K </k>
                 <out stream="stdout"> .List </out>
                

   rule test => function(T1,T2) when fresh(T1:Bool) andBool fresh(T2:Bool)
   rule <k> function(T:Bool,T) => .K ...</k>
        <out>... .List => ListItem("bad\n") </out>
   rule <k> function(T1:Bool,T2:Bool) => .K ...</k>
        <out>... .List => ListItem("good\n") </out>
     when T1 =/=K T2
endmodule
