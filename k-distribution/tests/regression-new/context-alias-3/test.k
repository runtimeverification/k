// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports INT

  syntax Foo ::= foo(Int)

  context alias [foo]: HERE
    requires isFoo(HOLE)

endmodule
