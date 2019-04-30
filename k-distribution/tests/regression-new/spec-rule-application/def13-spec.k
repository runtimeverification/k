require "def.k"

// X (in term) = Y (in pattern) matching.
// `requires Y ==Int incPos(Y) -Int 1` - Function in requires, used in LHS, same var as one matched in LHS.
module DEF13-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid Y => end Y </k>
         <var> _ </var>
      requires Y ==Int incPos(Y) -Int 1
      [trusted]

endmodule
