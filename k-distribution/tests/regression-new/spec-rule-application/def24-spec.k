// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// X+1 (in term) = Y (in pattern) matching.
// `<var> incPos(Y) +Int 1 </var>` - Function directly in another cell in LHS.
module DEF24-SPEC
    imports DEF

    claim <k> start X +Int 1 => end X </k>
         <var> X +Int 3 </var>
       requires X >=Int 0

    claim <k> mid Y => end Y -Int 1 </k>
         <var> incPos(Y) +Int 1 </var>
      [trusted]

endmodule
