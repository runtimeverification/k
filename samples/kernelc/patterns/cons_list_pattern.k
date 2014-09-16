// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS
  imports INT-SET

  syntax IntSeq ::= Int "::" IntSeq     [smtlib(smt_list_cons)]
                  | "[]"                [smtlib(smt_list_nil)]
                  > IntSeq "@" IntSeq   [function, left, smtlib(smt_list_concat)]
                  | "[" Int "]"         [function, smtlib(smt_list_elem)]
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

  syntax AssocIntSeq ::= AssocIntSeq @ 
  rule E::L => [E] @ L                    [smt-lemma]
  rule [] @ L => L                        [smt-lemma]
  rule L @ [] => L                        [smt-lemma]
  rule (L1 @ L2) @ L3 => L1 @ (L2 @ L3)   [smt-lemma]

  syntax IntSet ::= "intseq2intset" "(" IntSeq ")"    [function, smtlib(smt_seq2set)]
  rule intseq2intset(E::L) => { E } U intseq2intset(L)
  rule intseq2intset([]) => .IntSet

  syntax Bool ::= sorted(IntSeq)    [function]
  rule sorted(E::L) => { E } <=IntSet intseq2intset(L) andBool sorted(L)
  rule sorted([]) => true

  rule intseq2intset(L1 @ L2) => intseq2intset(L1) U intseq2intset(L2)
    [lemma]
  rule sorted(L1 @ L2)
    => intseq2intset(L1) <=IntSet intseq2intset(L2) andBool sorted(L1) andBool sorted(L2)
    [lemma]

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

  /* slseg pattern */
/*
  syntax Map ::= "slseg" "(" Pointer "," Pointer ")" "(" IntSet ")"    [pattern(2)]
  rule slseg(object(P:Int), Q:Pointer)({ E:Int } U S:IntSet)
    => object(P) |-> (
          val  |-> tv(int, E)
          next |-> tv(struct listNode *, ?PNext:Pointer))
       slseg(?PNext, Q)(S)
    requires object(P) =/=K Q
    [pattern]
  rule slseg(P:Pointer, P)(.IntSet) => .Map
    [pattern]

  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, null))
       F:Map
    => slseg(P, null)({ E })
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       (Q |-> M:Map)
       F:Map
    => slseg(P, Q)({ E })
       (Q |-> M)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, E:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       slseg(Q, null)(S:IntSet)
       F:Map
    => slseg(P, Q)({ E })
       slseg(Q, null)(S)
       F
    [pattern-folding]
  rule slseg(P:Pointer, Q:Pointer)(S1:IntSet)
       slseg(Q, null)(S2:IntSet)
       F:Map
    => slseg(P, null)(S1 U S2)
       F
    [pattern-folding]
  rule slseg(P:Pointer, R:Pointer)(S1:IntSet)
       slseg(R, Q:Pointer)(S2:IntSet)
       (Q |-> M:Map)
       F:Map
    => slseg(P, Q)(S1 U S2)
       (Q |-> M)
       F
    [pattern-folding]
  rule slseg(P:Pointer, R:Pointer)(S1:IntSet)
       slseg(R, Q:Pointer)(S2:IntSet)
       slseg(Q, null)(S3:IntSet)
       F:Map
    => slseg(P, Q)(S1 U S2)
       slseg(Q, null)(S3)
       F
    [pattern-folding]
*/
endmodule

