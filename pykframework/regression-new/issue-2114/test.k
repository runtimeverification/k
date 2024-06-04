// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
 imports A
endmodule

module A
  imports B
endmodule

module B
  imports private C
  rule foo() => .K
endmodule

module C
  syntax Foo ::= foo()
endmodule
