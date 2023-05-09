// Copyright (c) K Team. All Rights Reserved.
module MISSINGKLABEL-SYNTAX
endmodule

module MISSINGKLABEL
  imports MISSINGKLABEL-SYNTAX
  imports BASIC-K

  syntax MyMap ::= KItem "M|->" KItem
      [ function, total, hook(MAP.element), klabel(_M|->_), symbol, injective, unused]

  syntax MyMap ::= MyMap MyMap
      [ left, function, hook(MAP.concat), klabel(_MyMap_), symbol, assoc, comm
      , unit(.MyMap), element(_M|->_), format(%1%n%2), unused
      ]

endmodule
