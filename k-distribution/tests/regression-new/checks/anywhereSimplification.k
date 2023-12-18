// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module ANYWHERESIMPLIFICATION

  syntax Foo  ::= a() | b()

  rule a() => b() [anywhere, simplification]

endmodule
