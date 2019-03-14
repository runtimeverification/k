// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module TEST1-SPEC
  imports MAP-TESTS

  rule <k> .Map [ x <- 3 ] => x |-> 3 </k>
  rule <k> (X:MyId |-> 3) [ X <- 4 ] => X |-> 4 </k>

// TODO: Write tests for MAP-SYMBOLIC module:

// initalMap  (3 |-> 4   3*X |-> 5) /\ X > 1. During the execution, the program keep updating location 4*X in the map. so the map becomes (3 |-> 4   3*X |-> 5) ( (4*X |-> ...) [4*X <- ...] [4*X <- ...]). And now I'd like to lookup 4*X
// Given term (K1 |-> V1) (MAP [ K2 <- V2 ]), and I want to lookup K2, how would it work?
// Add test which checks that if you can't prove disjointness of initial map entries, critical error.
endmodule
