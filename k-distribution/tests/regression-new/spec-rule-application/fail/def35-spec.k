require "def.k"

// X (in term) = Y-1 (in pattern) matching.
// `requires incPos(Y) ==Int Y +Int 1` - Function in requires that is not substitution.
module DEF35-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid Y -Int 1 => end Y -Int 1 </k>
         <var> _ </var>
      requires incPos(Y) ==Int Y +Int 1
      [trusted]

endmodule
