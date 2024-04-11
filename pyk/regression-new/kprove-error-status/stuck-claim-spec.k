// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module VERIFICATION
  imports VERIF
endmodule

module STUCK-CLAIM-SPEC
  imports VERIFICATION

  claim  <k> addCounter(N:Int) => 1 ...</k>
         <counter> C:Int => ?_ </counter>
         <sum> S:Int => ?S:Int </sum>
    requires
      N >=Int 0
    ensures
      ?S ==Int S +Int N *Int C +Int (N -Int 1) *Int N /Int 2
endmodule
