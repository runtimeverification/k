module CHECKFUNCNOEVALUATORS-SYNTAX
  imports INT-SYNTAX
  syntax Thing ::= "thing" [function]
  syntax Another ::= "another" [function]
  syntax NoEvals ::= "noEvals" [function, no-evaluators]
endmodule

module CHECKFUNCNOEVALUATORS
    imports CHECKFUNCNOEVALUATORS-SYNTAX
endmodule
