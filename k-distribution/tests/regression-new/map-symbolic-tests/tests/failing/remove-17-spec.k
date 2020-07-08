// Copyright (c) 2019 K Team. All Rights Reserved.

requires "../map-tests.k"

module REMOVE-17-SPEC
    imports MAP-TESTS

    rule <k> remove ( (X:MyId |-> 3 y |-> 4) [ x <- undef ] [ X ] ) => . </k> requires X =/=K y

endmodule
