// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X+1 (in term) = Y (in pattern) matching.
//`requires Z ==Int incPos(Y)` - Function in requires, used in another cell in LHS.
module DEF22-SPEC
    imports DEF

    claim <k> start X +Int 1 => end X </k>
         <var> X +Int 3 </var>
       requires X >=Int 0

    claim <k> mid Y => end Y -Int 1 </k>
         <var> Z +Int 1 </var>
      requires Z ==Int incPos(Y)
      [trusted]

endmodule
