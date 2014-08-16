// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module HEAD-SPEC
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
            head |-> functionBody ( struct listNode * x , int , {  {
                return (x -> val) ; } return tv ( void , undef ) ; } )
        ...</fun>
        <k>
            head(x) => tv(int, Y:Int)
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
            list(object(P))(Y:Int :: ?L:Seq)
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
