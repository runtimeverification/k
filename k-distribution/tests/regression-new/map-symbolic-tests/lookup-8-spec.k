// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-8-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (MAP:Map X:MyId |-> 1) [Y:MyId <- 2] [ Z:MyId ] ) =>   lookupResult ( MAP [ Z <- 2 ]  ( X |-> 1 ) [ Z ] )  </k> requires Y =/=K X andBool Z  ==K Y andBool Z =/=K X

endmodule
