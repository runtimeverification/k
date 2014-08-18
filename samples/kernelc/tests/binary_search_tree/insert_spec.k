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
      insert |-> functionBody(
          int v, struct treeNode * t,
          struct treeNode *,
          {
            {
              if ( (t == tv ( void * , null )) )
                return (new_node ( v )) ;
              else ;
              if ( (v < (t -> value)) )
                (t -> left) = (insert ( v, (t -> left) )) ;
              else if ( (v > (t -> value)) )
                (t -> right) = (insert ( v, (t -> right) )) ;
              else ;
              return t ;
            }
            return tv ( void , undef ) ;
          })
      new_node |-> functionBody(
          int v,
          struct treeNode *,
          {
            {
              struct treeNode * node ;
              node = (( struct treeNode * ) (malloc ( (sizeof ( struct treeNode )) ))) ;
              (node -> value) = v ;
              (node -> left) = tv ( void * , null ) ;
              (node -> right) = tv ( void * , null ) ;
              return node ;
            }
            return tv ( void , undef ) ;
          })
    ...</fun>
    <k>
      insert(tv(int, V:Int), tv(struct treeNode *, TP1:Pointer))
    =>
      tv(struct treeNode *, ?TP2:Pointer)
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
      tree(TP1)(T1:Tree) => tree(?TP2)(?T2:Tree)
    ...</heap>
    <in>
      _:List
    </in>
    <out>
      _:List
    </out>
  </config>
requires bst(T1)
ensures bst(?T2) andBool tree_keys(?T2) ==K { V } U tree_keys(T1)
endmodule

