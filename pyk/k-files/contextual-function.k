module CONTEXTUAL-FUNCTION-SYNTAX
    imports INT-SYNTAX

    syntax Int ::= getCtx() [function, functional]
endmodule


module CONTEXTUAL-FUNCTION
    imports CONTEXTUAL-FUNCTION-SYNTAX
    imports INT

    configuration <k> $PGM:KItem </k>
                  <ctx> 0 </ctx>

    rule [[ getCtx() => N ]]
         <ctx> N </ctx>
      [label(def-get-ctx)]
endmodule
