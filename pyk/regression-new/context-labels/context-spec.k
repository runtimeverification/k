// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "context.k"

module CONTEXT-SPEC
  imports CONTEXT

  claim <k> foo( a, a ) => foo( 0, 0 ) ... </k>

  claim <k> bar( a, a ) => bar( 0, 0 ) ... </k>

  claim <k> baz( a, a ) => baz( a, 0 ) ... </k>

endmodule
