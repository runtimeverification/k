// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module INT-LIST
  imports LIST
  imports INT-SET

  rule size(L1:List L2:List) => size(L1) +Int size(L2)    [lemma]
  rule size(ListItem(_)) => 1                             [lemma]
  rule size(.List) => 0                                   [lemma]

  syntax Int ::= sum(List)                            [function, smtlib(smt_seq_sum)]
  rule sum(L1:List L2:List) => sum(L1) +Int sum(L2)   [lemma]
  rule sum(ListItem(I:Int)) => I                      [lemma]
  rule sum(.List) => 0                                [lemma]

  syntax List ::= rev(List)                       [function]
  rule rev(L1:List L2:List) => rev(L2) rev(L1)    [lemma]
  rule rev(ListItem(I:Int)) => ListItem(I:Int)    [lemma]
  rule rev(.List) => .List                        [lemma]

/*
  syntax IntSeq ::= filterList(Int, IntSeq)   [function, smtlib(smt_seq_filter)]
  rule filterIntSeq(V, L1 @ L2) => filterIntSeq(V, L1) @ filterIntSeq(V, L2)    [lemma]
  // TODO(AndreiS): this lemma is put directly in z3 because of ite issue
  //rule filterIntSeq(V, [E]) => #if V =/=K E #then [E] #else [] #fi              [lemma]
  rule filterIntSeq(V, []) => []                                                [lemma]
*/

  syntax IntSet ::= list2set(List)   [function, smtlib(smt_seq2set)]
  rule list2set(L1:List L2:List) => list2set(L1) U list2set(L2)
    [lemma, smt-lemma]
  rule list2set(ListItem(I:Int)) => { I }   [lemma, smt-lemma]
  rule list2set(.List) => .IntSet           [lemma, smt-lemma]

  syntax Bool ::= sorted(List)    [function, smtlib(smt_seq_sorted)]
  // TODO(AndreiS): add support for specifying Z3 triggers
  //rule sorted(L1 @ L2)
  //  => intseq2intset(L1) <=IntSet intseq2intset(L2) andBool sorted(L1) andBool sorted(L2)
  //  [smt-lemma]
  rule sorted(ListItem(I)) => true    [smt-lemma]
  rule sorted(.List) => true          [smt-lemma]
endmodule

