// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module RULES
  rule
    <threads>
      <thread>
        <id> 0 </id>
        <k>
while (n0 > 0) {
  f0 = 1;
  turn = 1;
  while(f1 == 1 && turn != 0) {}
  x = x + 1;
  n0 = n0 - 1;
  f0 = 0;
}
    =>
      .K
        </k>
      </thread>
      <thread>
        <id> 1 </id>
        <k>
while (n1 > 0) {
  f1 = 1;
  turn = 0;
  while(f0 == 1 && turn == 0) {}
  x = x + 1;
  n1 = n1 - 1;
  f1 = 0;
}
    =>
      .K
        </k>
      </thread>
    </threads>
    <state>...
      n0 |-> (N0:Int => 0)
      n1 |-> (N1:Int => 0)
      x |-> (X:Int => X:Int +Int N0:Int +Int N1:Int)
      f0 |-> 0
      f1 |-> 0
      turn |-> (T:Int => _:Int)
    ...</state>
  when N0:Int >=Int 0 andBool N1:Int >=Int 0
endmodule

