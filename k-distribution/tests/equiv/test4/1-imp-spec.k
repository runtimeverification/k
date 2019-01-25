// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module PLUS-IMP-SPEC
imports IMP

syntax Id ::= "x" [token]
            | "y" [token]

rule
<L1>
     <k> addi(x,y) </k>
     <state> ... x |-> N:Int y |-> M:Int ... </state>
</L1>
ensures vars(ListItem(N) ListItem(M))

rule
<L1>
     <k> I:Int </k>
     <state> _:Map </state>
</L1>
ensures vars(ListItem(I) ListItem(0))
[trusted]

endmodule
