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
      delete |-> functionBody(
          int v, struct treeNode * t,
          struct treeNode *,
          {
            {
              int min ;
              if ( (t == tv ( void * , null )) )
                return tv ( void * , null ) ;
              else ;
              if ( (v == (t -> value)) ) {
                if ( ((t -> left) == tv ( void * , null )) ) {
                  struct treeNode * temp ;
                  temp = (t -> right) ;
                  (free ( t )) ;
                  return temp ;
                } else if ( ((t -> right) == tv ( void * , null )) ) {
                  struct treeNode * temp ;
                  temp = (t -> left) ;
                  (free ( t )) ;
                  return temp ;
                } else {
                  min = (find_min ( (t -> right) )) ;
                  (t -> right) = (delete ( min, (t -> right) )) ;
                  (t -> value) = min ;
                }
              } else if ( (v < (t -> value)) )
                (t -> left) = (delete ( v, (t -> left) )) ;
              else
                (t -> right) = (delete ( v, (t -> right) )) ;
              return t ;
            }
            return tv ( void , undef ) ;
          })
      find_min |-> functionBody(
          struct treeNode * t,
          int,
          {
            {
              if ( ((t -> left) == tv ( void * , null )) )
                return (t -> value) ;
              else
                return (find_min ( (t -> left) )) ;
            }
            return tv ( void , undef ) ;
          })
    ...</fun>
    <k>
      delete(tv(int, V:Int), tv(struct treeNode *, TP1:Pointer))
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
ensures bst(?T2) andBool tree_keys(?T2) ==K tree_keys(T1) -IntSet { V }

rule
  <config>
    <struct>...
      treeNode |-> (
        (value |-> int)
        (left  |-> struct treeNode *)
        (right |-> struct treeNode *))
    ...</struct>
    <fun>...
      delete |-> functionBody(
          int v, struct treeNode * t,
          struct treeNode *,
          {
            {
              int min ;
              if ( (t == tv ( void * , null )) )
                return tv ( void * , null ) ;
              else ;
              if ( (v == (t -> value)) ) {
                if ( ((t -> left) == tv ( void * , null )) ) {
                  struct treeNode * temp ;
                  temp = (t -> right) ;
                  (free ( t )) ;
                  return temp ;
                } else if ( ((t -> right) == tv ( void * , null )) ) {
                  struct treeNode * temp ;
                  temp = (t -> left) ;
                  (free ( t )) ;
                  return temp ;
                } else {
                  min = (find_min ( (t -> right) )) ;
                  (t -> right) = (delete ( min, (t -> right) )) ;
                  (t -> value) = min ;
                }
              } else if ( (v < (t -> value)) )
                (t -> left) = (delete ( v, (t -> left) )) ;
              else
                (t -> right) = (delete ( v, (t -> right) )) ;
              return t ;
            }
            return tv ( void , undef ) ;
          })
      find_min |-> functionBody(
          struct treeNode * t,
          int,
          {
            {
              if ( ((t -> left) == tv ( void * , null )) )
                return (t -> value) ;
              else
                return (find_min ( (t -> left) )) ;
            }
            return tv ( void , undef ) ;
          })
    ...</fun>
    <k>
      find_min(tv(struct treeNode *, TP:Pointer))
    =>
      tv(int, ?M:Int)
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
requires TP =/=K null andBool bst(T)
ensures (?M inIntSet tree_keys(T)) andBool ({ ?M } <=IntSet tree_keys(T))
endmodule

