// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module RULES
  rule
    <k>
    return ((a > b) ? a : b => V:Float);
    </k>
    <state>...
      a |-> A:Float
      b |-> B:Float
    ...</state>
  requires true
  ensures A >Float B impliesBool V ==Float A
endmodule

