module IMP
configuration <T>
  <k> init ~> store(0,0,10) ~> $PGM:Int </k>
  <store> .Map </store>
</T>

syntax KItem ::= array(Map)

syntax KItem ::= store(Int,Int,Int)
rule <k> store(L:Int, K:Int, V:Int) => .K ... </k>
     <store> L |-> array(M:Map => M[K <- V]) ... </store>

syntax KItem ::= "init"
rule <k> init => .K ... </k>
     <store> (.Map =>
       0 |-> array(.Map)
     ) </store>

endmodule
