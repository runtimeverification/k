require "def.k"

// `requires Z ==Int incPos(Y)` - Function in requires, used in RHS. Does not affect matching.
module DEF02-SPEC
    imports DEF

    claim <k> start X => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    claim <k> mid Y => end ?Z </k>
         <var> _ </var>
      requires ?Z ==Int incPos(Y)
      [trusted]

endmodule
