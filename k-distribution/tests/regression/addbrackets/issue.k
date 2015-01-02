// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module ISSUE

syntax A ::= "++" A | String "++" | String | Int | B | C | A A
syntax B ::= Int "++" [klabel('foo)]
syntax C ::= Int "++" [klabel('bar)]
syntax D ::= Int "++" Int

syntax E ::= "*" "*"
syntax F ::= "*"
syntax G ::= F F F | E F | F E
syntax H ::= E "*" | "*" E

endmodule
