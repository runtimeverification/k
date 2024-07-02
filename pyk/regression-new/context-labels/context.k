// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CONTEXT
  imports INT

  syntax KResult ::= Int

  syntax A ::= "a" | Int
             | foo( A, A ) [seqstrict, klabel(foo)]
             | bar( A, A )
             | baz( A, A ) [strict(2), klabel(baz)]

  context [bar1]: bar( HOLE,    _ )
  context [bar2]: bar(    _, HOLE )

  rule a => 0

endmodule
