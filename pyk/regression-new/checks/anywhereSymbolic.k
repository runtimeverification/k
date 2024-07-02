// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module ANYWHERESYMBOLIC

  syntax Foo  ::= a() | b()

  rule a() => b() [anywhere, symbolic]

endmodule
