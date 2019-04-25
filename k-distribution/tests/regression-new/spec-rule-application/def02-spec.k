require "def.k"

// `requires Z ==Int incPos(Y)` - Function in requires, used in RHS. Does not affect matching.
module DEF02-SPEC
    imports DEF

    rule <k> start X => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid Y => end Z </k>
         <var> _ </var>
      requires Z ==Int incPos(Y)
      [trusted]

endmodule
