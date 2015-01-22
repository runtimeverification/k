// Copyright (c) 2014-2015 K Team. All Rights Reserved.
DEF: null -> null
module TEST
  syntax Foo ::= "m"

  syntax Foo ::= "t"

  syntax Foo ::= "u"

  syntax Foo ::= "x"

  syntax Foo ::= "y"

  syntax Foo ::= "z"

  syntax left 'm 't

  syntax priorities'x
> 'y 'z
> 'm 't
> 'u

  syntax right 'u


endmodule

