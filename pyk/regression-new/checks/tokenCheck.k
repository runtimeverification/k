// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TOKENCHECK-SYNTAX
  imports ID-SYNTAX
  syntax X ::= "abc" [token]

endmodule

module TOKENCHECK
  imports TOKENCHECK-SYNTAX
  imports INT

  syntax X ::= fail()

  syntax Y ::= "a" [token]
  syntax Y ::= Z
  syntax Z ::= "b" [token]

  syntax Int ::= "foo" [macro]
  rule foo => 3

  syntax Id ::= Foo(Id)
endmodule
