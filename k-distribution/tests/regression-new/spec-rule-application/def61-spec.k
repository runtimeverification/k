// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

/*
Part 6. Term must be always simplified/evaluated under current constraint.
==============
61.
    k:          X1 matches Y1
    var part 1: X2 matches incPos(Y2)
    var part 2: X2 - 1 matches Y2 +Int (incPos(Y1) -Int Y1 -Int 1) - Evaluates to Y2. Must be preferred over c2.
*/
module DEF61-SPEC
    imports DEF

    claim <k> start X1 => end X1 </k>
         <var> binop X2 (X2 -Int 1) </var>
       requires X1        >=Int 0
        andBool X2 -Int 1 >=Int 0

    claim <k> mid Y1 => end Y1 </k>
         <var> binop incPos(Y2) (Y2 +Int (incPos(Y1) -Int Y1 -Int 1)) </var>
      [trusted]

endmodule
