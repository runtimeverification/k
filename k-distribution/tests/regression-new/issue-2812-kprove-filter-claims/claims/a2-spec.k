requires "test.k"


module VERIFICATION
  import TEST
  rule [s1]: notAFunction => 1 [simplification]

  claim <k> run(5) => .K </k> <counter> n => 0 </counter>
endmodule

module A2-SPEC
  import VERIFICATION
endmodule
