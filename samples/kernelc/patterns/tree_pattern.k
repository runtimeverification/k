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
endmodule

