// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

// 2 equalities can generate mutually exclusive substitutions.
// Situation similar to what is found in ERC2.0 high-level contract
//    k  : X matches incPos(Y) -Int 1
//    var: X matches Y - should have priority
module DEF44-SPEC
    imports DEF

    claim <k> start X => end X </k>
         <var> X </var>
       requires X >=Int 0

    claim <k> mid incPos(Y) -Int 1 => end Y </k>
         <var> Y </var>
      [trusted]

endmodule
