// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X+1 (in term) = Y (in pattern) matching.
// `requires Y ==Int incPos(Y) -Int 1` - Function in requires, used in LHS, same var as one matched in LHS.
module DEF23-SPEC
    imports DEF

    claim <k> start X +Int 1 => end X </k>
         <var> _ </var>
       requires X >=Int 0

    claim <k> mid Y => end Y -Int 1 </k>
         <var> _ </var>
      requires Y ==Int incPos(Y) -Int 1
      [trusted]

endmodule
