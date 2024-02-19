// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module DUPLICATEATTRULE

  syntax Foo  ::= a()
  rule a() => .K [concrete, concrete]

endmodule
