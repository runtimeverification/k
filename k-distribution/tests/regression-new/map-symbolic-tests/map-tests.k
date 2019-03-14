// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module MAP-TESTS-SYNTAX
    imports MAP
    imports INT

    syntax MyId ::= "x" | "y" | "z"
endmodule

module MAP-TESTS
  imports MAP-TESTS-SYNTAX

  configuration <k> $PGM:Map </k>
endmodule
