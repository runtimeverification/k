// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIFICATION
  imports BMC

endmodule


module FAIL-TEST2-SPEC-BMC
  imports VERIFICATION
  imports BMC

  rule (<T> <k> #execute </k> <state> "x" |-> X </state> </T>) #Implies (#AG(#Forall Y . #Forall _ .((<T> <k> #execute </k> <state> "x" |-> Y </state> </T>) #Implies {X ==Int Y #Equals true})))  [kore]

endmodule
