// Copyright (c) 2014 K Team. All Rights Reserved.

module TREE-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS

  syntax Tree ::= "node" "(" Int "," Tree "," Tree ")"
                | "leaf"

  syntax Set ::= "tree_keys" "(" Tree ")"   [function]
  rule tree_keys(node(I:Int, TL:Tree, TR:Tree))
    => SetItem(I) tree_keys(TL) tree_keys(TR)
  rule tree_keys(leaf) => .Set
  syntax Int ::= "tree_height" "(" Tree ")"   [function]
  rule tree_height(node(I:Int, TL:Tree, TR:Tree))
    => 1 +Int maxInt(tree_height(TL), tree_height(TR))
  rule tree_height(leaf) => 0

  syntax Map ::= "tree" "(" Pointer ")" "(" Tree ")"    [pattern(1)]
  rule tree(object(P:Int))(node(I:Int, TL:Tree, TR:Tree))
    => object(P) |-> (
          value |-> tv(int, I)
          left  |-> tv(struct treeNode *, ?PL:Pointer)
          right |-> tv(struct treeNode *, ?PR:Pointer))
       tree(?PL)(TL)
       tree(?PR)(TR)
    [pattern]
  rule tree(null)(leaf) => .Map   [pattern]

  /*
  syntax Bool ::= bst(Tree)   [function]
  rule bst(node(I:Int, TL:Tree, TR:Tree))
    => lt(tree_keys(TL), SetItem(I)) andBool lt(SetItem(I), tree_keys(TR))
       andBool bst(TL) andBool bst(TR)
  rule bst(leaf) => true
  */
endmodule

