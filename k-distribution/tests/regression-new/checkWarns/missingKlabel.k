module MISSINGKLABEL-SYNTAX
endmodule

module MISSINGKLABEL
  imports MISSINGKLABEL-SYNTAX

  syntax MyMap ::= MyMap MyMap
      [ left, function, hook(MAP.concat), klabel(_MyMap_), symbol, assoc, comm
      , unit(.MyMap), element(_M|->_), index(0), format(%1%n%2), unused
      ]

endmodule
