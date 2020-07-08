// Copyright (c) 2019 K Team. All Rights Reserved.

requires "../map-tests.k"

module LOOKUP-23-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (X:MyId |-> 3 y |-> 4) [ x <- 5 ] [ X ] ) => . </k> requires X =/=K y

endmodule
