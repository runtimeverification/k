// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS
  imports INT-LIST

  /* list pattern */
  syntax Map ::= "list" "(" Pointer ")" "(" List ")"    [pattern(1)]
  rule
    list(object(P:Int))(ListItem(I:Int) L:List)
  =>
    object(P) |-> (
        val  |-> tv(int, I)
        next |-> tv(struct listNode *, ?PNext:Pointer))
    list(?PNext)(L)
    [pattern]
  rule list(null)(.List) => .Map
    [pattern]

  /* lseg pattern */
  syntax Map ::= "lseg" "(" Pointer "," Pointer ")" "(" List ")"    [pattern(2)]
  rule lseg(object(P:Int), Q:Pointer)(ListItem(I:Int) L:List)
    => object(P) |-> (
          val  |-> tv(int, I)
          next |-> tv(struct listNode *, ?PNext:Pointer))
       lseg(?PNext, Q)(L)
    requires object(P) =/=K Q
    [pattern]
  rule lseg(P:Pointer, P)(.List) => .Map
    [pattern]

  rule P:Pointer |-> (
          val  |-> tv(int, I:Int)
          next |-> tv(struct listNode *, null))
       F:Map
    => lseg(P, null)(ListItem(I))
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, I:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       (Q |-> M:Map)
       F:Map
    => lseg(P, Q)(ListItem(I))
       (Q |-> M)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, I:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       lseg(Q, null)(L:List)
       F:Map
    => lseg(P, Q)(ListItem(I))
       lseg(Q, null)(L)
       F
    [pattern-folding]
  rule P:Pointer |-> (
          val  |-> tv(int, I:Int)
          next |-> tv(struct listNode *, Q:Pointer))
       lseg(Q, R:Pointer)(L:List)
       R |-> M:Map
       F:Map
    => lseg(P, Q)(ListItem(I))
       lseg(Q, R)(L)
       R |-> M:Map
       F
    [pattern-folding]
  rule lseg(P:Pointer, Q:Pointer)(L1:List)
       lseg(Q, null)(L2:List)
       F:Map
    => lseg(P, null)(L1 L2)
       F
    [pattern-folding]
  rule lseg(P:Pointer, R:Pointer)(L1:List)
       lseg(R, Q:Pointer)(L2:List)
       (Q |-> M:Map)
       F:Map
    => lseg(P, Q)(L1 L2)
       (Q |-> M)
       F
    [pattern-folding]
  rule lseg(P:Pointer, R:Pointer)(L1:List)
       lseg(R, Q:Pointer)(L2:List)
       lseg(Q, null)(L3:List)
       F:Map
    => lseg(P, Q)(L1 L2)
       lseg(Q, null)(L3)
       F
    [pattern-folding]
endmodule

