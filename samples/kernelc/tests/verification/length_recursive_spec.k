// Copyright (c) 2014 K Team. All Rights Reserved.
require "../../kernelc.k"

module LENGTH-RECURSIVE-SPEC
  imports KERNELC

/* */
rule
    <config>
        <struct>
            listNode |-> (
                (next |-> struct listNode *)
                (val  |-> int)
            )
        </struct>
        <fun>
            length_recursive |-> functionBody ( struct listNode * x , int , {  {
              if ( (x == NULL) ) return 0 ; else ; return (1 + (length_recursive ( (x
               -> next) ))) ; } return tv ( void , undef ) ; } )
        ...</fun>
        <k>
            if ( (x == NULL) ) return 0 ; else ; return (1 + (
            length_recursive ( (x -> next) ))) ;
              =>
            return tv(int, len(A)) ; ~> _:K // YilongL: ` ~> _:K` is neccessary to prove the base case
        ...</k>
        <env>
            x |-> tv ( struct listNode * * , object ( Lx:Int ) )
        ...</env>
        <fun-id>
            length_recursive
        </fun-id>
        <stack>
            _:List
        </stack>
        <heap>
            object(Lx) |-> tv (struct listNode *, P:Pointer)
            list(P)(A:Seq)
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
            length_recursive |-> functionBody ( struct listNode * x , int , {  {
              if ( (x == NULL) ) return 0 ; else ; return (1 + (length_recursive ( (x
               -> next) ))) ; } return tv ( void , undef ) ; } )
        ...</fun>
        <k>
            length_recursive ( x ) => tv(int, len(A))
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
            list(P)(A:Seq)
        ...</heap>
        <in>
            _:List
        </in>
        <out>
            _:List
        </out>
    </config>

endmodule
