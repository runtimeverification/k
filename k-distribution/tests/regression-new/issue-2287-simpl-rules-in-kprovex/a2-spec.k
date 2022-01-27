requires "test.k"


module VERIFICATION
  import TEST

  rule <k> (X +Int Y) +Int Z => Z +Int (X +Int Y) </k> [simplification, symbolic(X), concrete(Y, Z)]
  rule notAFunction => 1 [simplification]
endmodule

module A2-SPEC
  import VERIFICATION

  claim [s1]:
    <k> run(5) => .K </k> <counter> n => 0 </counter>

endmodule
