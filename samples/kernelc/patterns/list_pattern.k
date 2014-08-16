// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports KERNELC-SEMANTICS

  syntax Seq ::= Int "::" Seq
               | "[]"
  syntax Seq ::= Seq "@" Seq      [function]
               | rev(Seq)         [function]
  syntax Int ::= len(Seq)         [function]
  rule (E::L1) @ L2 => E::(L1 @ L2)
  rule [] @ L => L
  rule rev(E::L) => rev(L) @ E::[]
  rule rev([]) => []
  rule len(E::L) => 1 +Int len(L)
  rule len([]) => 0

  /* lemmas */
  rule L @ [] => L                                [lemma]
  rule (L1 @ (E :: [])) @ L2 => L1 @ (E :: L2)    [lemma]

  syntax Map ::= "list" "(" Pointer ")" "(" Seq ")"   [pattern(1)]
  rule
    list(object(P:Int))(E:Int::L:Seq)
  =>
    object(P) |-> (
        val  |-> tv(int, E)
        next |-> tv(struct listNode *, ?PNext:Pointer))
    list(?PNext)(L)
  [pattern]
  rule list(null)([]) => .Map
  [pattern]

endmodule
