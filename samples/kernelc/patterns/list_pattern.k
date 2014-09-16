// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS
  imports INT-SET

  syntax IntSeq ::= IntSeq "@" IntSeq   [function, left, smtlib(smt_seq_concat)]
                  | "[]"                [function, smtlib(smt_seq_nil)]
                  | "[" Int "]"         [function, smtlib(smt_seq_elem), klabel(smt_seq_elem)]

  syntax Int ::= len(IntSeq)            [function, smtlib(smt_seq_len)]
               | sum(IntSeq)            [function, smtlib(smt_seq_sum)]
  rule len(L1 @ L2) => len(L1) +Int len(L2)   [lemma]
  rule len([E]) => 1                          [lemma]
  rule len([]) => 0                           [lemma]
  rule sum(L1 @ L2) => sum(L1) +Int sum(L2)   [lemma]
  rule sum([E]) => E                          [lemma]
  rule sum([]) => 0                           [lemma]

  syntax IntSeq ::= rev(IntSeq)             [function]
  rule rev(L1 @ L2) => rev(L2) @ rev(L1)    [lemma]
  rule rev([E]) => [E]                      [lemma]
  rule rev([]) => []                        [lemma]
  //rule rev(rev(L) => L                      [lemma]

  syntax IntSeq ::= filterIntSeq(Int, IntSeq)   [function, smtlib(smt_seq_filter)]
  rule filterIntSeq(V, L1 @ L2) => filterIntSeq(V, L1) @ filterIntSeq(V, L2)    [lemma]
  // TODO(AndreiS): this lemma is put directly in z3 because of ite issue 
  //rule filterIntSeq(V, [E]) => #if V =/=K E #then [E] #else [] #fi              [lemma]
  rule filterIntSeq(V, []) => []                                                [lemma]

  /* lemmas */
  rule [] @ L => L                        [lemma, smt-lemma]
  rule L @ [] => L                        [lemma, smt-lemma]
  rule (L1 @ L2) @ L3 => L1 @ (L2 @ L3)   [lemma, smt-lemma]

  rule L1 @ L2 ==K [] => L1 ==K [] andBool L2 ==K []    [smt-lemma]
  rule [_] ==K [] => false                              [smt-lemma]

  syntax IntSet ::= "intseq2intset" "(" IntSeq ")"    [function, smtlib(smt_seq2set)]
  rule intseq2intset(L1 @ L2) => intseq2intset(L1) U intseq2intset(L2)
    [lemma, smt-lemma]
  rule intseq2intset([E]) => { E }    [lemma, smt-lemma]
  rule intseq2intset([]) => .IntSet   [lemma, smt-lemma]

  syntax Bool ::= sorted(IntSeq)    [function, smtlib(smt_seq_sorted)]
  //rule sorted(L1 @ L2)
  //  => intseq2intset(L1) <=IntSet intseq2intset(L2) andBool sorted(L1) andBool sorted(L2)
  //  [smt-lemma]
  rule sorted([E]) => true    [smt-lemma]
  rule sorted([]) => true     [smt-lemma]

  /* conversion between IntSeq and List */
  syntax List ::= intseq2list(IntSeq)   [function]
  rule intseq2list([E]) => ListItem(E)                            [lemma]
  rule intseq2list([]) => .List                                   [lemma]
  rule intseq2list(L1 @ L2) => intseq2list(L1) intseq2list(L2)    [lemma]

  syntax IntSeq ::= list2intseq(List)   [function]
  rule list2intseq(ListItem(H) L:List) => [H] @ list2intseq(L)
  rule list2intseq(.List) => []

  /* list pattern */
  syntax Map ::= "list" "(" Pointer ")" "(" IntSeq ")"      [pattern(1)]
  rule
    list(object(P:Int))([E:Int] @ L:IntSeq)
  =>
    object(P) |-> (
        val  |-> tv(int, E)
        next |-> tv(struct listNode *, ?PNext:Pointer))
    list(?PNext)(L)
    [pattern]
  rule list(null)([]) => .Map
    [pattern]

  /* lseg pattern */
  syntax Map ::= "lseg" "(" Pointer "," Pointer ")" "(" IntSeq ")"    [pattern(2)]
  rule lseg(object(P:Int), Q:Pointer)([E:Int] @ L:IntSeq)
    => object(P) |-> (
          val  |-> tv(int, E)
          next |-> tv(struct listNode *, ?PNext:Pointer))
       lseg(?PNext, Q)(L)
    requires object(P) =/=K Q
    [pattern]
  rule lseg(P:Pointer, P)([]) => .Map
    [pattern]

  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, null))
       F:Map
    => lseg(P, null)([E])
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       (Q |-> M:Map)
       F:Map
    => lseg(P, Q)([E])
       (Q |-> M)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       lseg(Q, null)(L:IntSeq)
       F:Map
    => lseg(P, Q)([E])
       lseg(Q, null)(L)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       lseg(Q, R:Pointer)(L:IntSeq)
       R |-> M:Map
       F:Map
    => lseg(P, Q)([E])
       lseg(Q, R)(L)
       R |-> M:Map
       F
    [pattern-folding]
  rule lseg(P:Pointer, Q:Pointer)(L1:IntSeq)
       lseg(Q, null)(L2:IntSeq)
       F:Map
    => lseg(P, null)(L1 @ L2)
       F
    [pattern-folding]
  rule lseg(P:Pointer, R:Pointer)(L1:IntSeq)
       lseg(R, Q:Pointer)(L2:IntSeq)
       (Q |-> M:Map)
       F:Map
    => lseg(P, Q)(L1 @ L2)
       (Q |-> M)
       F
    [pattern-folding]
  rule lseg(P:Pointer, R:Pointer)(L1:IntSeq)
       lseg(R, Q:Pointer)(L2:IntSeq)
       lseg(Q, null)(L3:IntSeq)
       F:Map
    => lseg(P, Q)(L1 @ L2)
       lseg(Q, null)(L3)
       F
    [pattern-folding]
endmodule

