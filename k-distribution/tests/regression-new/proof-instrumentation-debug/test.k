// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST-SYNTAX
  syntax Foo ::= foo() | bar()
endmodule

module TEST
  imports TEST-SYNTAX
  rule foo() => bar()
endmodule
