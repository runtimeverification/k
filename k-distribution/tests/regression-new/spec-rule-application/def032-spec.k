// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X = Y-1, `mid Y => end incPos(Y)` - Function in pattern RHS.
module DEF032-SPEC
    imports DEF

    claim <k> start X => end X +Int 2 </k>
         <var> _ </var>
       requires X >=Int 0

    claim <k> mid Y -Int 1 => end incPos(Y) </k>
         <var> _ </var>
      [trusted]

endmodule
