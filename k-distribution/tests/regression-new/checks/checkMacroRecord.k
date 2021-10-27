// https://github.com/kframework/k/issues/2217
// do not generate sort projections for macro symbols
module CHECKMACRORECORD
    imports INT

    configuration <k> $PGM:Int </k>

    syntax Int ::= f ( a: Int, b: Int )
 // -----------------------------------
    rule f(X, Y) => X +Int Y [macro]

endmodule
