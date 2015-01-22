// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  syntax Foo ::= "t"

  syntax Foo ::= "u"

  syntax Foo ::= "x"

  syntax Foo ::= "y"

  syntax Foo ::= "z"

  syntax left 'x

  syntax priorities'x
> 'y 'z
> 't
> 'u

  syntax right 'y


endmodule

