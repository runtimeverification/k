// Copyright (c) 2022 K Team. All Rights Reserved.

module CEIL-SET-SYNTAX
    imports SET
    imports K-EQUAL
    imports BOOL

    syntax Test ::= eval ( Set ) | evalResult ( Set )
endmodule

module CEIL-SET
    imports SET-TESTS-SYNTAX

    configuration <k> $PGM:Test </k>

    rule <k> eval ( S ) => evalResult ( S ) </k>

    rule #Ceil(@S1:Set @S2:Set) => {intersectSet(@S1, @S2) #Equals .Set} #And #Ceil(@S1) #And #Ceil(@S2)
      [anywhere, simplification]

endmodule
