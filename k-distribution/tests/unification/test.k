// Copyright (c) 2012-2018 K Team. All Rights Reserved.

requires "unification.k"

module TEST
    imports LIST
    imports MATCHING
    imports UNIFICATION

    configuration
        <k> $PGM:Problems </k>
        <results> .List </results>

    syntax Exp ::= Exp "+" Exp
                 | Int
                 | "symbolicExp" [function]
 // ---------------------------------------
    rule symbolicExp => ?E:Exp

    syntax Problems ::= List{Problem,""}
 // ------------------------------------
    rule <k> .Problems    => .       ... </k>
    rule <k> P:Problem P' => P ~> P' ... </k>

    syntax Problem ::= Exp "matches" Exp "?"
 // ----------------------------------------
    rule <k> E1 matches E2 ? => . ... </k>
         <results> ... (.List => ListItem(#matches(E2,E1))) </results>

    syntax Problem ::= "unify" Exp "and" Exp
    syntax K       ::= "unify" "(" Exp "," Exp ")" "is" K
 // -----------------------------------------------------
    rule <k> unify E and E' => . ... </k>
         <results> ... (.List => ListItem(unify (E , E') is #unify(E, E'))) </results>
endmodule
