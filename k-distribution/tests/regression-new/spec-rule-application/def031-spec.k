require "def.k"

// X = Y,   `mid Y => end incPos(Y)` - Function in pattern RHS.
module DEF031-SPEC
    imports DEF

    rule <k> start X => end X +Int 1 </k>
         <var> _ </var>
       requires X >=Int 0

    rule <k> mid Y => end incPos(Y) </k>
         <var> _ </var>
      [trusted]

endmodule
