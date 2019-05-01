require "def.k"

// inc(Y) in pattern LHS. Function with no side conditions.
module DEF01-SPEC
    imports DEF

    rule <k> start X => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid Y => end inc(Y) </k>
         <var> _ </var>
      [trusted]

endmodule
