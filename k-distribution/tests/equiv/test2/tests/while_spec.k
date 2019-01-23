// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module IMP-SPEC
imports IMP

// simple loop
rule
<T>
<L1>
  <k>
    while (n <= 10) {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L1>
<L2>
  <k>
    while (n <= 10) {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L2>
</T>

// simple loop with symbolic bound
rule
<T>
<L1>
  <k>
    while (n <= sum) {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
    sum |-> S:Int
  ...</state>
</L1>
<L2>
  <k>
    while (n <= sum) {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
    sum |-> S:Int
  ...</state>
</L2>
</T>

/* non-equivalent loops: note that `<=` is used
rule
<T>
<L1>
  <k>
    while (n <= 10) {
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int +Int N:Int
  ...</state>
</L1>
<L2>
  <k>
    while (n <= 10) {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int +Int N:Int
  ...</state>
</L2>
</T>
*/

// loop squashing
rule
<T>
<L1>
  <k>
    while (!(10 <= n)) { // n < 10
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int +Int N:Int
  ...</state>
</L1>
<L2>
  <k>
    while (!(10 <= n)) { // n < 10
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int +Int N:Int
  ...</state>
</L2>
</T>

// loop squashing 2
rule
<T>
<L1>
  <k>
    while (!(10 <= n)) { // n < 10
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L1>
<L2>
  <k>
    while (!(10 <= n)) { // n < 10
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> M:Int
  ...</state>
</L2>
</T>
requires N modInt 2 ==K 0
andBool M modInt 2 ==K 0
andBool N ==K M

rule
<T>
<L1>
  <k>
    .K
  </k>
  <state>...
    n   |-> ?N1:Int
  ...</state>
</L1>
<L2>
  <k>
    .K
  </k>
  <state>...
    n   |-> ?N2:Int
  ...</state>
</L2>
</T>
requires ?N1 ==K ?N2
 [trusted]

endmodule
