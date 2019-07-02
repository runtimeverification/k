// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports BMC

endmodule


module FAIL-TEST1-SPEC-BMC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> 6 </state> </T>) #Implies (#AG (#Forall X . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies {X <Int 10 #Equals true})))  [kore]

endmodule
