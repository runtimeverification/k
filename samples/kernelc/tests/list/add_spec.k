// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module ADD-SPEC
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
            add |-> functionBody ( int v, struct listNode * x , struct listNode *
              , {  { struct listNode * y ; y = (( struct listNode * ) (malloc ( (
              sizeof ( struct listNode )) ))) ; (y -> val) = v ; (y -> next) = x ;
               return y ; } return tv ( void , undef ) ; } )
        //...</fun> // TODO(YilongL): had to disable `...` to forbid the prover
                    // applying function call rule on `malloc` operation which
                    // generates UnsuppportedOperationException's and leads to
                    // illegal states which can not be proved
        </fun>
        <k>
            //add(v, x) => tv(struct listNode *, object(?Ly:Int))
            add(v, x) => tv(struct listNode *, ?Y:Pointer)
        ...</k>
        <env>
            v |-> tv ( int * , object ( Lv:Int ) )
            x |-> tv ( struct listNode * * , object ( Lx:Int ) )
        ...</env>
        <fun-id>
            _:Id
        </fun-id>
        <stack>
            _:List
        </stack>
        <heap>
            object(Lv) |-> tv (int, V:Int)
            object(Lx) |-> tv (struct listNode *, P:Pointer)
            (list(P)(L:Seq) => list(?Y)(V::L))
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
