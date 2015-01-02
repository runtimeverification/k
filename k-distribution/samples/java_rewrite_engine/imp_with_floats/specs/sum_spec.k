// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module RULES
  rule
    <k>
while (n > 0.0) {
  sum = sum + n;
  n = n - 1.0;
}
    =>
      .K
    </k>
    <state>...
      n |-> (N:Float => 0.0)
      sum |-> (
          ((N0:Float -Float N:Float) *Float (N0:Float +Float N:Float +Float 1.0)) /Float 2.0
        =>
          (N0:Float *Float (N0:Float +Float 1.0)) /Float 2.0)
    ...</state>
  when 0.0 <=Float N:Float <=Float 100.0
endmodule

