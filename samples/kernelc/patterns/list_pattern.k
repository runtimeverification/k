// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS

  syntax IntSeq ::= Int "::" IntSeq
                  | "[]"
                  > IntSeq "@" IntSeq   [function, left]
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

endmodule
