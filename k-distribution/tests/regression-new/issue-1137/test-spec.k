// Copyright (c) 2019 K Team. All Rights Reserved.
module VERIFICATION
  imports VERIF
  syntax Bool ::= isA(S) [function, functional]
endmodule


module TEST-SPEC
    imports VERIFICATION

    rule <k> X:S => b ... </k>
      requires isA(X)
endmodule
