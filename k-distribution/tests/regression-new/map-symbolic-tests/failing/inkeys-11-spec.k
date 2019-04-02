// Copyright (c) 2019 K Team. All Rights Reserved.

requires "../map-tests.k"

module INKEYS-11-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( Y:MyId in_keys ( Z:MyId |-> 1 M:Map X:MyId |-> 0 ) ) => . </k> requires notBool Y in_keys(M)

endmodule
