// Copyright (c) 2014-2015 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports SIMPLE-UNTYPED-SEMANTICS

  syntax Seq ::= Int "::" Seq
               | "[]"
  syntax Seq ::= Seq "@" Seq      [function]
               | rev(Seq)         [function]
  rule (E::L1) @ L2 => E::(L1 @ L2)
  rule [] @ L => L
  rule rev(E::L) => rev(L) @ E::[]
  rule rev([]) => []

  /* lemmas */
  rule L @ [] => L                                [lemma]
  rule (L1 @ (E :: [])) @ L2 => L1 @ (E :: L2)    [lemma]

  syntax Map ::= "list" "(" Val ")" "(" Seq ")"   [pattern(1)]
  rule
    list(array(X:Int, 2))(E:Int::L:Seq)
  =>
    X |-> E
    X +Int 1 |-> ?Y:Val
    list(?Y)(L)
  [pattern]
  rule list(0)([]) => .Map
  [pattern]

endmodule

