module NOEVALUATORSEXHAUSTIVE-SYNTAX
    imports INT-SYNTAX
    syntax Int ::= foo ( Int ) [function, total, no-evaluators]
endmodule

module NOEVALUATORSEXHAUSTIVE
    imports NOEVALUATORSEXHAUSTIVE-SYNTAX
    rule <k> 0 => foo(0) </k>
endmodule
