// Copyright (c) 2014 K Team. All Rights Reserved.
require "kernelc.k"

module AVL-SPEC
  imports KERNELC

rule
  <fun>... FUN:Map ...</fun>
  <k>
    max(tv(int, X:Int), tv(int, Y:Int))
  =>
    tv(int, maxInt(X, Y))
  ...</k>

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    height(tv(struct node *, TP:Pointer))
  =>
    tv(int, tree_height(T))
  ...</k>
  <heap>... htree(TP)(T:Tree) ...</heap>
requires avl(T)

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    update_height(tv(struct node *, object(P:Int)))
  =>
    tv(void, undef)
  ...</k>
  <heap>...
    object(P) |-> (
        value  |-> tv(int, I:Int)
        height |-> tv(int, _:Int => tree_height(node(I, TL, TR)))
        left   |-> tv(struct node *, PL:Pointer)
        right  |-> tv(struct node *, PR:Pointer))
    htree(PL)(TL:Tree)
    htree(PR)(TR:Tree)
  ...</heap>
requires avl(TL) andBool avl(TR)

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    find_min(tv(struct node *, TP:Pointer))
  =>
    tv(int, ?M:Int)
  ...</k>
  <heap>... htree(TP)(T:Tree) ...</heap>
requires TP =/=K null andBool avl(T)
ensures (?M inIntSet tree_keys(T)) andBool ({ ?M } <=IntSet tree_keys(T))

rule
  <struct>... STRUCT:Map ...</struct>
  <fun>... FUN:Map ...</fun>
  <k>
    delete(tv(int, V:Int), tv(struct node *, TP1:Pointer))
  =>
    tv(struct node *, ?TP2:Pointer)
  ...</k>
  <heap>... htree(TP1)(T1:Tree) => htree(?TP2)(?T2:Tree) ...</heap>
requires avl(T1)
ensures avl(?T2) andBool tree_keys(?T2) ==K tree_keys(T1) -IntSet { V }
  andBool tree_height(T1) -Int 1 <=Int tree_height(?T2)
  andBool tree_height(?T2) <=Int tree_height(T1)
endmodule

