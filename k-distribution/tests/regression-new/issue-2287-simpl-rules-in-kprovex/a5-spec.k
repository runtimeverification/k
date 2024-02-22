// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"
// https://github.com/runtimeverification/k/issues/2587

module A5-SPEC
  imports TEST
  imports ML-SYNTAX

  claim <k> c => 2 #And n +Int n </k>
  rule n +Int n => #Top [simplification, comm]
  // the comm attribute is stripped because it has a different meaning in the backend
  // even if comm, the body is identical so we don't generate anything extra
endmodule
