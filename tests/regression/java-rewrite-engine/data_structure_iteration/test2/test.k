require "builtins/set.k"
require "builtins/map.k"

module TEST
  imports SET
  imports MAP

  configuration
    <k> $PGM ~> .MySet </k>
    <state>
      0 |-> (MySetItem(0), MySetItem(1)),
      1 |-> (MySetItem(1), MySetItem(2)),
      .MyMap
    </state>

  rule
    <k> K:Int ~> (.MySet => MySetItem(V)), _:MySet </k>
    <state>... K |-> ((MySetItem(V:Int) => .MySet), _:MySet) ...</state>
endmodule

