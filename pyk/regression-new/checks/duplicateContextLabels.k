// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module DUPLICATECONTEXTLABELS
  imports INT

  syntax KResult ::= Int
  syntax A ::= "a"
             | foo( A, A )

  context [foo-left]:  foo( HOLE,    _ )
  context [foo-right]: foo(    _, HOLE )

  rule [foo-left-cool]: a => 1

endmodule
