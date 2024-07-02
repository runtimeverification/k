// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module ATTPARAMFORBIDDEN

  syntax Foo  ::= a()
  rule a() => .K [owise(1)]

endmodule
