// Copyright (c) 2014 K Team. All Rights Reserved.

module TREE-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS

  syntax IntSet ::= IntSet "U" IntSet           [function, smtlib(smt_set_cup)]
                  | ".IntSet"                   [function, smtlib(smt_set_emp)]
                  | "{" Int "}"                 [function, smtlib(smt_set_sin), klabel(smt_set_sin)]
                  | IntSet "-IntSet" IntSet     [function, smtlib(smt_set_dif)]
  syntax Bool ::= Int "inIntSet" IntSet         [function, smtlib(smt_set_mem)]
                | IntSet  "<IntSet" IntSet      [function, smtlib(smt_set_lt)]
                | IntSet "<=IntSet" IntSet      [function, smtlib(smt_set_le)]
  rule I:Int inIntSet (S1:IntSet U S2:IntSet)
    => (I inIntSet S1) orBool (I inIntSet S2)
    [lemma]
  rule _:Int inIntSet .IntSet => false                  [lemma]
  rule I1:Int inIntSet { I2:Int } => I1 ==K I2          [lemma]
  rule S:IntSet <IntSet (S1:IntSet U S2:IntSet)
    => (S:IntSet <IntSet S1:IntSet) andBool (S:IntSet <IntSet S2:IntSet)
    [lemma]
  rule (S1:IntSet U S2:IntSet) <IntSet S:IntSet
    => (S1:IntSet <IntSet S:IntSet) andBool (S2:IntSet <IntSet S:IntSet)
    [lemma]
  rule _:IntSet <IntSet .IntSet => true                 [lemma]
  rule .IntSet <IntSet _:IntSet => true                 [lemma]
  rule { I1:Int } <IntSet { I2:Int } => I1 <Int I2      [lemma]
  rule S:IntSet <=IntSet (S1:IntSet U S2:IntSet)
    => (S:IntSet <=IntSet S1:IntSet) andBool (S:IntSet <=IntSet S2:IntSet)
    [lemma]
  rule (S1:IntSet U S2:IntSet) <=IntSet S:IntSet
    => (S1:IntSet <=IntSet S:IntSet) andBool (S2:IntSet <=IntSet S:IntSet)
    [lemma]
  rule _:IntSet <=IntSet .IntSet => true                [lemma]
  rule .IntSet <=IntSet _:IntSet => true                [lemma]
  rule { I1:Int } <=IntSet { I2:Int } => I1 <=Int I2    [lemma]
  rule .IntSet -IntSet _:IntSet => .IntSet              [lemma]

  syntax Tree ::= "node" "(" Int "," Tree "," Tree ")"
                | "leaf"

  syntax IntSet ::= "tree_keys" "(" Tree ")"    [function, smtlib(smt_tree_keys)]
  rule tree_keys(node(I:Int, TL:Tree, TR:Tree))
    => { I } U (tree_keys(TL) U tree_keys(TR))
  rule tree_keys(leaf) => .IntSet
  syntax Int ::= "tree_height" "(" Tree ")"     [function, smtlib(smt_tree_height)]
  rule tree_height(node(I:Int, TL:Tree, TR:Tree))
    => 1 +Int maxInt(tree_height(TL), tree_height(TR))
  rule tree_height(leaf) => 0
  syntax Int ::= "tree_size" "(" Tree ")"       [function, smtlib(smt_tree_size)]
  rule tree_size(node(_:Int, TL:Tree, TR:Tree))
    => 1 +Int tree_size(TL) +Int tree_size(TR)
  rule tree_size(leaf) => 0
  syntax Tree ::= "tree_mirror" "(" Tree ")"    [function, smtlib(smt_tree_mirror)]
  rule tree_mirror(node(I:Int, TL:Tree, TR:Tree))
    => node(I, tree_mirror(TR), tree_mirror(TL))
  rule tree_mirror(leaf) => leaf
  syntax List ::= "tree2list" "(" Tree ")"      [function]//, smtlib(smt_tree2list)] // YilongL: sort List is reserved in Z3
  rule tree2list(node(I:Int, TL:Tree, TR:Tree))
    => tree2list(TL) ListItem(I) tree2list(TR)
  rule tree2list(leaf) => .List

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

  syntax Bool ::= bst(Tree)   [function, smtlib(smt_bst)]
  rule bst(node(I:Int, TL:Tree, TR:Tree))
    => tree_keys(TL) <IntSet { I } andBool { I } <IntSet tree_keys(TR)
       andBool bst(TL) andBool bst(TR)
  rule bst(leaf) => true

  syntax Map ::= "htree" "(" Pointer ")" "(" Tree ")"   [pattern(1)]
  rule htree(object(P:Int))(node(I:Int, TL:Tree, TR:Tree))
    => object(P) |-> (
          value  |-> tv(int, I)
          height |-> tv(int, tree_height(node(I:Int, TL:Tree, TR:Tree)))
          left   |-> tv(struct node *, ?PL:Pointer)
          right  |-> tv(struct node *, ?PR:Pointer))
       htree(?PL)(TL)
       htree(?PR)(TR)
    [pattern]
  rule htree(null)(leaf) => .Map   [pattern]

  syntax Bool ::= avl(Tree)   [function, smtlib(smt_avl)]
  rule avl(node(I:Int, TL:Tree, TR:Tree))
    => tree_keys(TL) <IntSet { I } andBool { I } <IntSet tree_keys(TR)
       andBool absInt(tree_height(TL) -Int tree_height(TR)) <=Int 1
       andBool avl(TL) andBool avl(TR)
  rule avl(leaf) => true

  rule tree_height(T:Tree) >=Int 0 => true    [smt-lemma]

  // TODO(YilongL): should probably go somewhere else; needs a better name...
  syntax Int ::= bool2Int(Bool)                 [function, smtlib(smt_bool2int)]
  rule bool2Int(true) => 1
  rule bool2Int(false) => 0
endmodule
