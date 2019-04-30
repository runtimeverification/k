require "def.k"

// X (in term) = Y (in pattern) matching.
// `<var> incPos(Y) +Int 1 </var>` - Function directly in another cell in LHS.
module DEF14-SPEC
    imports DEF

    rule <k> start X => end X </k>
         <var> X +Int 2 </var>
       requires X >=Int 0

    rule <k> mid Y => end Y </k>
         <var> incPos(Y) +Int 1 </var>
      [trusted]

endmodule
