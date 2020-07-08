// Copyright (c) 2019 K Team. All Rights Reserved.

requires "../map-tests.k"

module REMOVE-15-SPEC
    imports MAP-TESTS

    rule <k> remove ( (MAP:Map X:MyId |-> 1) [Y:MyId <- undef] [ Z:MyId ] ) => . </k> requires Z =/=K Y andBool Z  ==K X andBool Y =/=K X

endmodule
