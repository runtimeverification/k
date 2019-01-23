// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module IMP-SPEC
imports IMP

// simple constant propagation
rule
<T>
<L1>
  <k>
    if (n <= 0) {
      n = n + 1;
    } else {
      n = n + 1;
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L1>
<L2>
  <k>
    if (n <= 0) {
      n = n + 1;
    } else {
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L2>
</T>

// swap if-then-else branch
rule
<T>
<L1>
  <k>
    if (!(n <= 0)) {
      n = n + 1;
      n = n + 1;
    } else {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L1>
<L2>
  <k>
    if (n <= 0) {
      n = n + 1;
    } else {
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L2>
</T>

// simple code motion
rule
<T>
<L1>
  <k>
    n = n + 1;
    if (n <= 0) {
    } else {
      n = n + 1;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L1>
<L2>
  <k>
    if (n <= 0) {
      n = n + 1;
    } else {
      n = n + 2;
    }
  </k>
  <state>...
    n   |-> N:Int
  ...</state>
</L2>
</T>

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
