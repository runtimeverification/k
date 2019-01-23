// Copyright (c) 2014-2019 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  syntax Foo ::= "m"

  syntax Foo ::= "t"

  syntax Foo ::= "u"

  syntax Foo ::= "x"

  syntax Foo ::= "y"

  syntax Foo ::= "z"

  syntax left t m

  syntax prioritiesx
> y z
> t m
> u

  syntax right u


endmodule

