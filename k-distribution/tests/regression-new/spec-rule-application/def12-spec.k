require "def.k"

// X (in term) = Y (in pattern) matching.
// `requires Z ==Int incPos(Y)` - Function in requires, used in another cell in LHS.
module DEF12-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> X +Int 2 </var>
       requires X >=Int 0

    rule <k> mid Y => end Y </k>
         <var> Z +Int 1 </var>
      requires Z ==Int incPos(Y)
      [trusted]

endmodule
