// Copyright (c) 2021 K Team. All Rights Reserved.

requires "test.k"

module TEST-SPEC
    imports TEST

  claim
    <k> #assert i ( 1 , 0 ) ==Int 0 => . </k>
      requires true #And ( #Forall X. { i ( X, 0 ) #Equals 0 } )

endmodule
