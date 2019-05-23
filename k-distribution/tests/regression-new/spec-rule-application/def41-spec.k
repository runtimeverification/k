require "def.k"

/*
Part 4. Substitutions of RHS vars must be preferred over LHS vars, for cases var = term
==============
    - e.g. if we have to chose between LHSVar = term and RHSVar = term, RHSVar must be preferred.
41. Unifying equalities
    RHSVar = term in <k>   , has priority
    LHSVar = term in <var>
*/
module DEF41-SPEC
    imports DEF

    rule <k> start X -Int 1 => end X -Int 1 </k>
         <var> X </var>
       requires X -Int 1 >=Int 0

    rule <k> mid Y => end Y </k>
         <var> incPos(Y) </var>
      [trusted]

endmodule
