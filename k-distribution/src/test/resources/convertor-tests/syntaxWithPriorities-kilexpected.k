// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
DEF: null -> null
module TEST
  syntax Foo ::= "t"

  syntax Foo ::= "u"

  syntax Foo ::= "x"

  syntax Foo ::= "y"

  syntax Foo ::= "z"

  syntax left x

  syntax priorityx
> y z
> t
> u

  syntax right y


endmodule

