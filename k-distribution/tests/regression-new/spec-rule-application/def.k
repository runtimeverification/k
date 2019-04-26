module DEF
    imports INT

    syntax Term ::= "start" Int
                  | "mid"   Int
                  | "end"   Int
                  | "aux"   Term //use to control level of nesting
                  | "binop" Term Term
                  | Int

    configuration <T>
      <k> $PGM:K </k>
      <var> 0:Term </var>
    </T>

    rule start X => mid X

    syntax Int ::= inc(Int)            [function]
    rule inc(X) => X +Int 1

    syntax Int ::= incPos(Int)         [function]
    rule incPos(X) => X +Int 1
      requires X >=Int 0

    rule (X +Int A) +Int B => X +Int (A +Int B)
    rule (X +Int A) -Int B => X +Int (A -Int B)
    rule (X -Int A) +Int B => X +Int (B -Int A)
      requires B =/=Int 0
    rule X +Int (A -Int X) => A
    rule X +Int 0 => X

endmodule
