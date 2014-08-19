// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module DEALLOCATE-SPEC
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
            deallocate |-> functionBody ( struct listNode * x , void , {  {  while
               ( (x != tv ( void * , null )) ) { struct listNode * y ; y = (x ->
              next) ; (free ( x )) ; x = y ; } } return tv ( void , undef ) ; } )
        //...</fun> // YilongL: avoid narrowing the `...` when evaluating the `free` function
        </fun>
        <k>
            while ( (x != tv ( void * , null )) ) { struct listNode * y ;
            y = (x -> next) ; (free ( x )) ; x = y ; }
              =>
            .K
        ...</k>
        <env>
            x |-> tv ( struct listNode * * , object ( Lx:Int ))
        ...</env>
        <fun-id>
            deallocate
        </fun-id>
        <stack>
            _:List
        </stack>
        <heap>
            object(Lx) |-> tv (struct listNode *, P:Pointer => null)
            (list(P)(L:Seq) => .Map)
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

rule
    <config>
        <struct>
            listNode |-> (
                (next |-> struct listNode *)
                (val  |-> int)
            )
        </struct>
        <fun>
            deallocate |-> functionBody ( struct listNode * x , void , {  {  while
               ( (x != tv ( void * , null )) ) { struct listNode * y ; y = (x ->
              next) ; (free ( x )) ; x = y ; } } return tv ( void , undef ) ; } )
        //...</fun>
        </fun>
        <k>
            deallocate(x) => tv(void, undef)
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
            object(Lx) |-> tv (struct listNode *, P:Pointer /* TODO(YilongL): cannot write `P:Pointer => null`; seems like a problem of the KernelC semantics itself */)
            (list(P)(L:Seq) => .Map)
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
