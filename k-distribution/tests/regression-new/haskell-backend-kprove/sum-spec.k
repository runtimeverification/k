module VERIFICATION
  imports VERIF
endmodule

module SUM-SPEC
  import VERIFICATION

  rule  <k> addCounter(N:Int) => . ...</k>
        <counter> C:Int => ?_ </counter>
        <sum> S:Int => ?S:Int </sum>
    requires
      N >=Int 0
    ensures
      ?S ==Int S +Int N *Int C +Int (N -Int 1) *Int N /Int 2
endmodule