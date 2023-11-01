// Copyright (c) K Team. All Rights Reserved.
module DUPLICATEATTRULE

  syntax Foo  ::= a()
  rule a() => .K [concrete, concrete]

endmodule
