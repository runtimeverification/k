// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-24-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (y |-> 4) [ x ] ==K 4 ) => . </k>

endmodule
