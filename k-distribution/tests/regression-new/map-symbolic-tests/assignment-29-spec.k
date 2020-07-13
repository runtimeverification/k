// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-29-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (       X:MyId   |-> BAL_TO:Int       Y:MyId   |-> BAL_FROM:Int MAP:Map ) [       Y   <- BAL_FROM -Int 30 ] ) => . </k> requires       X   =/=K       Y

endmodule
