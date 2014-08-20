// Copyright (c) 2014 K Team. All Rights Reserved.
require "kernelc.k"

module BST-SPEC
  imports KERNELC

rule
  <config>
    <struct>...
      treeNode |-> (
        (value |-> int)
        (left  |-> struct treeNode *)
        (right |-> struct treeNode *))
    ...</struct>
    <fun>...
      find |-> functionBody(
        int v, struct treeNode * t,
        int,
        {
          {
            if ( (t == tv ( void * , null )) )
              return 0 ;
            else if ( (v == (t -> value)) )
              return 1 ;
            else if ( (v < (t -> value)) )
              return (find ( v, (t -> left) )) ;
            else return (find ( v, (t -> right) )) ;
          }
          return tv (void , undef ) ;
        })
    ...</fun>
    <k>
      find(tv(int, V:Int), tv(struct treeNode *, TP:Pointer))
    =>
      tv(int, ?B:Int)
    ...</k>
    <env>
      _:Map
    </env>
    <fun-id>
      _:Id
    </fun-id>
    <stack>
      _:List
    </stack>
    <heap>...
      tree(TP)(T:Tree)
    ...</heap>
    <in>
      _:List
    </in>
    <out>
      _:List
    </out>
  </config>
requires bst(T)
ensures (?B =/=K 0) ==K (V inIntSet tree_keys(T))
endmodule

