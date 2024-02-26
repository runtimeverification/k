// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module MISSINGKLABEL-SYNTAX
endmodule

module MISSINGKLABEL
  imports MISSINGKLABEL-SYNTAX
  imports BASIC-K

  syntax MyMap ::= KItem "M|->" KItem
      [ function, total, hook(MAP.element), symbol(_M|->_), injective, unused]

  syntax MyMap ::= MyMap MyMap
      [ left, function, hook(MAP.concat), symbol(_MyMap_), assoc, comm
      , unit(.MyMap), element(_M|->_), index(0), format(%1%n%2), unused
      ]

endmodule
