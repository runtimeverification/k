requires "test.k"


module VERIFICATION
  import TEST

  claim [s1]:
    <k> 1 => 2 </k> // should fail but marked as trusted whould pass

endmodule

module A1-SPEC
  import VERIFICATION

endmodule
