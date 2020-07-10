// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-30-SPEC
    imports MAP-TESTS

    rule <k> assignment ( ( foo ( X:MyId ) |-> BAL_TO:Int foo ( Y:MyId ) |-> BAL_FROM:Int MAP:Map ) [ foo ( Y ) <- BAL_FROM -Int 30 ] ) => assignmentResult ( MAP  foo ( X ) |-> BAL_TO  foo ( Y ) |-> BAL_FROM -Int 30 ) </k> requires       X   =/=K       Y   // implicit: foo ( X ) =/=K foo ( Y )

endmodule
