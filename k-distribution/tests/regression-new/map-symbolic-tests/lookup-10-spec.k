// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-10-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (MAP:Map X:MyId |-> 1) [Y:MyId <- 2] [ Z:MyId ] ) =>   lookupResult ( ( MAP  Z |-> 1 ) [ Y <- 2 ] [ Z ] )  </k> requires Z  ==K X

endmodule
