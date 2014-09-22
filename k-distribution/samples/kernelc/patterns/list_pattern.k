// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS
  imports INT-LIST

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

