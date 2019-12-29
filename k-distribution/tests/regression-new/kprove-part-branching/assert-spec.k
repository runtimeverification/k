// Copyright (c) 2019 K Team. All Rights Reserved.

//Test that 2 vars with the same name but different sort are distinct.
//Before te fix they got mixed up in the [trusted] rules, in Java Backend, due to function caching+spec rule pre-processing.

requires "assert.k"

module ASSERT-SPEC
  imports ASSERT

  rule <k> assert (A ==Int 0) => . </k>

endmodule
