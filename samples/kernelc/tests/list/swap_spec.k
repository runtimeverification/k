// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module SWAP-SPEC
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
            swap |-> functionBody ( struct listNode * x , struct listNode * , {  {
               struct listNode * p ; p = x ; x = (x -> next) ; (p -> next) = (x ->
               next) ; (x -> next) = p ; return x ; } return tv ( void , undef ) ;
               } )
        ...</fun>
        <k>
            swap(x) => tv(struct listNode *, ?P:Pointer)
        ...</k>
        <env>
            x |-> tv ( struct listNode * * , object ( Lx:Int ) )
        ...</env>
        <fun-id>
            _:Id
        </fun-id>
        <stack>
            _:List
        </stack>
        <heap>
            object(Lx) |-> tv (struct listNode *, P:Pointer)
            (list(P)(V1:Int :: V2:Int :: L:Seq) => list(?P)(V2 :: V1 :: L))
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
