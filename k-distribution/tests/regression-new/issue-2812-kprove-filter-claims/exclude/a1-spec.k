// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "test.k"


module VERIFICATION
  imports TEST

  rule (X +Int Y) +Int Z => Z +Int (X +Int Y) [simplification, symbolic(X), concrete(Y, Z)]
  rule (X +Int Y) +Int Z => Y +Int (X +Int Z) [simplification, concrete(X, Z), symbolic(Y)]
  rule X +Int (Y +Int Z) => Z +Int (X +Int Y) [simplification, concrete(X, Y), symbolic(Z)]
  rule X +Int (Y +Int Z) => Y +Int (X +Int Z) [simplification, concrete(X, Z), symbolic(Y)]
  rule final(n +Int M:Int) => 0 requires M >=Int 0 [simplification, concrete(M)]

  claim [pass1]:
    <k> run(5) => .K </k> <counter> n => 0 </counter>
  claim [fail1]: <k> 1 => 2 </k>
  claim [fail2]: <k> 1 => 3 </k>

endmodule

module A1-SPEC
  imports VERIFICATION

endmodule
