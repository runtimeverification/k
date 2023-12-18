// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module RESTRICTEDATTS

  syntax Foo  ::= a() [cool, kore, left]
  rule a() => .K [idem, owise]

endmodule
