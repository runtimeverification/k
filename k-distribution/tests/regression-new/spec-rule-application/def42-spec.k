// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "def.k"

/*
Part 4. Substitutions of RHS vars must be preferred over LHS vars, for cases var = term
==============
    - e.g. if we have to chose between LHSVar = term and RHSVar = term, RHSVar must be preferred.

42. Unifying equalities
    LHSVar = term in <k>   , has priority
    RHSVar = term in <var>
*/
module DEF42-SPEC
    imports DEF

    claim <k> start X => end X </k>
         <var> X -Int 1 </var>
       requires X -Int 1 >=Int 0

    claim <k> mid incPos(Y) => end Y +Int 1 </k>
         <var> Y </var>
      [trusted]

endmodule
