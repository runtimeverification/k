// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module ATTPARAMREQUIRED

  syntax Foo  ::= a()
  rule a() => .K [prec]

endmodule
