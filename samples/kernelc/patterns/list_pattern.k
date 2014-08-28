// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS

  syntax IntSeq ::= Int "::" IntSeq     [smtlib(smt_list_cons)]
                  | "[]"                [smtlib(smt_list_nil)]
                  > IntSeq "@" IntSeq   [function, left, smtlib(smt_list_concat)]
                  | rev(IntSeq)         [function]
  syntax Int ::= len(IntSeq)            [function, smtlib(smt_list_len)]
               | sum(IntSeq)            [function, smtlib(smt_list_sum)]
  rule (E::L1) @ L2 => E::(L1 @ L2)
  rule [] @ L => L
  rule rev(E::L) => rev(L) @ E::[]
  rule rev([]) => []
  rule len(E::L) => 1 +Int len(L)
  rule len([]) => 0
  rule sum(E::L) => E +Int sum(L)
  rule sum([]) => 0

  /* lemmas */
  rule L @ [] => L                                      [lemma]
  rule (L1 @ L2) @ L3 => L1 @ (L2 @ L3)                 [lemma]
  rule rev(L1 @ L2) => rev(L2) @ rev(L1)                [lemma]

  /* conversion between IntSeq and List */
  syntax List ::= "intseq2list" "(" IntSeq ")"  [function]
  rule intseq2list(E:Int :: L:IntSeq)
    => ListItem(E) intseq2list(L)
  rule intseq2list([]) => .List
  rule intseq2list(L1 @ L2)
    => intseq2list(L1) intseq2list(L2)
  [lemma]

  syntax IntSeq ::= "list2intseq" "(" List ")"  [function]
  rule list2intseq(ListItem(H) L:List)
    => H :: list2intseq(L)
  rule list2intseq(.List) => []

  /* list pattern */
  syntax Map ::= "list" "(" Pointer ")" "(" IntSeq ")"      [pattern(1)]
  rule
    list(object(P:Int))(E:Int::L:IntSeq)
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
  rule lseg(object(P:Int), Q:Pointer)(E:Int::L:IntSeq)
    => object(P) |-> (
          val  |-> tv(int, E)
          next |-> tv(struct listNode *, ?PNext:Pointer))
       lseg(?PNext, Q)(L)
    requires object(P) =/=K Q
    //ensures object(P) =/=K ?PNext
    [pattern]
  rule lseg(P:Pointer, P)([]) => .Map
    [pattern]

  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, null))
       F:Map
    => lseg(P, null)(E::[])
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       (Q |-> M:Map)
       F:Map
    => lseg(P, Q)(E::[])
       (Q |-> M)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       lseg(Q, null)(L:IntSeq)
       F:Map
    => lseg(P, Q)(E::[])
       lseg(Q, null)(L)
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

  rule (E::L1) @ L2 => E::(L1 @ L2)       [smt-lemma]
  rule [] @ L => L                        [smt-lemma]
  rule L @ [] => L                        [smt-lemma]
  rule (L1 @ L2) @ L3 => L1 @ (L2 @ L3)   [smt-lemma]
endmodule

