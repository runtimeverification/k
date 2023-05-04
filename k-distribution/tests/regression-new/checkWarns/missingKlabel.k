// Copyright (c) K Team. All Rights Reserved.
module MISSINGKLABEL-SYNTAX
endmodule

module MISSINGKLABEL
  imports MISSINGKLABEL-SYNTAX

  syntax MyMap ::= MyMap MyMap
      [ left, function, hook(MAP.concat), klabel(_MyMap_), symbol, assoc, comm
      , unit(.MyMap), format(%1%n%2), unused
      ]

endmodule
