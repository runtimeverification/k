// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X+1 (in term) = Y (in pattern) matching.
// `requires incPos(Y) ==Int Y +Int 1` - Function in requires that is not substitution.
module DEF25-SPEC
    imports DEF

    claim <k> start X +Int 1 => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    claim <k> mid Y => end Y </k>
         <var> _ </var>
      requires incPos(Y) ==Int Y +Int 1
      [trusted]

endmodule
