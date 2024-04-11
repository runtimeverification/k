// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module INVALIDLABEL
  imports BOOL
  imports INT

  rule [foo`bar]: true => false
  rule false => true [label(foo bar)]
  rule 0 => 1 [label(foo`bar)]

endmodule
