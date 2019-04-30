require "def.k"

// X (in term) = Y-1 (in pattern) matching.
// `requires Z ==Int incPos(Y)` - Function in requires, used in another cell in LHS.
module DEF32-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> X +Int 3 </var>
       requires X >=Int 0

    rule <k> mid Y -Int 1 => end Y -Int 1 </k>
         <var> Z +Int 1 </var>
      requires Z ==Int incPos(Y)
      [trusted]

endmodule
