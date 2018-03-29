// Copyright (c) 2012-2018 K Team. All Rights Reserved.

requires "unification.k"

module TEST
    imports LIST
    imports UNIFICATION

    configuration
        <k> $PGM:UnificationProblems </k>
        <results> .List </results>

    syntax Exp ::= Exp "+" Exp
                 | Int
                 | "symbolicExp" [function]
 // ---------------------------------------
    rule symbolicExp => ?E:Exp

    syntax UnificationProblem  ::= "unify" Exp "and" Exp
    syntax UnificationProblems ::= List{UnificationProblem,""}
 // ----------------------------------------------------------
    rule <k> .UnificationProblems      => .         ... </k>
    rule <k> UP:UnificationProblem UP' => UP ~> UP' ... </k>

    syntax K ::= "unify" "(" Exp "," Exp ")" "is" K
 // -----------------------------------------------
    rule <k> unify E and E' => . ... </k>
         <results> ... (.List => ListItem(unify (E , E') is #unify(E, E'))) </results>
endmodule
