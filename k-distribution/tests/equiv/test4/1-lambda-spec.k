// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module PLUS-LAMBDA-SPEC
imports LAMBDA

syntax Id ::= "x" [token]
            | "y" [token]

rule
<L2>
     <k> addl(x,y) </k>
     <env> ... x |-> Lx:Int y |-> Ly:Int ... </env>
     <store> ... Lx |-> N:Int Ly |-> M:Int ... </store>
</L2>
ensures vars(ListItem(N) ListItem(M))

rule
<L2>
     <k> I:Int </k>
     <env> _:Map </env>
     <store> _:Map </store>
</L2>
ensures vars(ListItem(I) ListItem(0))
[trusted]

endmodule
