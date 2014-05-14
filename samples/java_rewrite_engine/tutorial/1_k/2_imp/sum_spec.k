// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module RULES
  rule
    <k>
while (n > 0) {
  sum = sum + n;
  n = n - 1;
}
    =>
      .K
    </k>
    <state>...
      n |-> (N:Int => 0)
      sum |-> (
          ((N0:Int -Int N:Int) *Int (N0:Int +Int N:Int +Int 1)) /Int 2
        =>
          (N0:Int *Int (N0:Int +Int 1)) /Int 2)
    ...</state>
  when N:Int >=Int 0
endmodule

