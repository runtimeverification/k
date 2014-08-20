// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module TAIL-SPEC
  imports KERNELC

rule
    <config>
        <struct>
            listNode |-> (
                (next |-> struct listNode *)
                (val  |-> int)
            )
        </struct>
        <fun>
            tail |-> functionBody ( struct listNode * x , struct listNode * ,
                {  { return (x -> next) ; } return tv ( void , undef ) ; } )
        ...</fun>
        <k>
            tail(x) => tv(struct listNode *, Next:Pointer)
        ...</k>
        <env>
            x |-> tv ( struct listNode * * , object ( I:Int ) )
        ...</env>
        <fun-id>
            _:Id
        </fun-id>
        <stack>
            _:List
        </stack>
        <heap>
            object(I) |-> tv (struct listNode *, object (P:Int))
            object(P) |-> (
                val  |-> tv(int, _:Int)
                next |-> tv(struct listNode *, Next)
            )
            list(Next)(L:Seq)
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
