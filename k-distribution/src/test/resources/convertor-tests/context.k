// Copyright (c) 2014-2015 K Team. All Rights Reserved.

require "include.k"

module TEST
  imports INCLUDE

  syntax Exp ::= Exp "+" Exp

  context HOLE + _

  context _ + HOLE
endmodule
