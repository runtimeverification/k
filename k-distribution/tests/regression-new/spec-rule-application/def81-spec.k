require "def.k"

/*
Part 8. Initial simplification must have access to pattern constraint (e.g. spec rule side condition),
            otherwise generated substitutions are sub-optimal.
==============
81.
    k:                X +Int 1 matches Y2 -Int 1
    var part 1:       X        matches Y1 -Int 1
    var part 2:       X +Int 1 matches incPos(Y1) -Int 1
    pattern requires: Y2 == Y1 +Int 1

*/
module DEF81-SPEC
    imports DEF

    rule <k> start X +Int 1 => end X +Int 1</k>
         <var> binop X (X +Int 1) </var>
       requires X        >=Int 0

    rule <k> mid Y2 -Int 1 => end Y2 -Int 1 </k>
         <var> binop (Y1 -Int 1) (incPos(Y1) -Int 1) </var>
      requires Y2 ==Int Y1 +Int 1
      [trusted]

endmodule
