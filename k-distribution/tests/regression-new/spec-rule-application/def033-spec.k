// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X+1 = Y, `mid Y => end incPos(Y)` - Function in pattern RHS.
module DEF033-SPEC
    imports DEF

    claim <k> start X +Int 1 => end X +Int 2 </k>
         <var> _ </var>
       requires X >=Int 0

    claim <k> mid Y => end incPos(Y) </k>
         <var> _ </var>
      [trusted]

endmodule
