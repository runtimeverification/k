module SMT
    imports INT
    imports BOOL

    configuration <k> $PGM:Pgm </k>

    syntax Pgm ::= Bool | Int

    syntax Int ::= chop ( Int )           [function, total, symbol(chop), smtlib(chop)]
    syntax Int ::= "pow256"               [alias] /* 2 ^Int 256 */

    rule pow256 => 115792089237316195423570985008687907853269984665640564039457584007913129639936
    rule chop ( I:Int ) => I modInt pow256 [concrete, smt-lemma]

endmodule
