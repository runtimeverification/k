// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module RESTRICTEDATTS

  syntax Foo  ::= a() [cool, left]
  rule a() => .K [idem, owise]

endmodule
