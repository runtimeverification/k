// Copyright (c) 2019 K Team. All Rights Reserved.

//Test that 2 vars with the same name but different sort are distinct.
//Before te fix they got mixed up in the [trusted] rules, in Java Backend, due to function caching+spec rule pre-processing.

requires "var-eq.k"

module VAR-EQ-SPEC
  imports VAR-EQ

  rule <k> VAR:ATerm => a3 ...</k> [trusted]
  rule <k> VAR:BTerm => b3 ...</k> [trusted]

  rule <k> a1 => a3 ...</k>
  rule <k> b1 => b3 ...</k>

endmodule
