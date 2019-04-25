require "def.k"

// X (in term) = Y (in pattern) matching.
// inc(Y) in pattern LHS. Function with no side conditions. Evaluation required for planned matching.
module DEF11-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid inc(Y) -Int 1 => end Y </k>
         <var> _ </var>
      [trusted]

endmodule
