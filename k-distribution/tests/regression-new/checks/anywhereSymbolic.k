// Copyright (c) K Team. All Rights Reserved.
module ANYWHERESYMBOLIC

  syntax Foo  ::= a() | b()

  rule a() => b() [anywhere, symbolic]

endmodule
