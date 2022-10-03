requires "test.k"


module VERIFICATION
  import TEST

  rule notAFunction => 1 [simplification]
endmodule

module A6-SPEC
  import VERIFICATION

  claim [s1]:
    <k> run(5) => .K </k> <counter> n => 0 </counter>

endmodule
