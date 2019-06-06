require "def.k"

/*
Part 7: Unification (with function evaluation) must be preferred over substitution, after each substituted var.
==============
71.
    k:          X1 matches (Y2 +Int (incPos(Y1) -Int Y1 -Int 1)), will get evaluated to Y2
            - 2nd substitution to be extracted.
    var part 1: X1 matches Y1 - first substitution to be extracted
    var part 2: X1+1 matches incPos(Y2)
        - RHS can be evaluated only when Y1 is substituted by X1, and Y2 is substituted by X1.
*/
module DEF71-SPEC
    imports DEF

    rule <k> start X1 => end X1 </k>
         <var> binop X1 X1 +Int 1 </var>
       requires X1        >=Int 0

    rule <k> mid (Y2 +Int (incPos(Y1) -Int Y1 -Int 1)) => end Y2 </k>
         <var> binop Y1 incPos(Y2) </var>
      [trusted]

endmodule
