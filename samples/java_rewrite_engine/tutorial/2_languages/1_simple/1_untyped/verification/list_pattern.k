// Copyright (c) 2014 K Team. All Rights Reserved.

module LIST-PATTERN
  imports MAP
  imports SIMPLE-UNTYPED-SEMANTICS

  syntax Seq ::= Int "::" Seq
               | "[]"
  syntax Seq ::= Seq "@" Seq      [function]
               | rev(Seq)         [function]

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

