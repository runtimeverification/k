require "def.k"

// X+1 (in term) = Y (in pattern) matching.
// inc(Y) in pattern LHS. Function with no side conditions. Evaluation required for planned matching.
module DEF21-SPEC
    imports DEF

    rule <k> start X +Int 1 => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid inc(Y) -Int 1 => end Y </k>
         <var> _ </var>
      [trusted]

endmodule
