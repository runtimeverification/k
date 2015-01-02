// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "builtins/set.k"
require "builtins/map.k"

module TEST
  imports SET
  imports MAP

  configuration
    <k> $PGM ~> .Set </k>
    <state>
      0 |-> (SetItem(0) SetItem(1))
      1 |-> (SetItem(1) SetItem(2))
    </state>

  rule
    <k> K:Int ~> (.Set => SetItem(V)) _:Set </k>
    <state>... K |-> ((SetItem(V:Int) => .Set) _:Set) ...</state>
endmodule

