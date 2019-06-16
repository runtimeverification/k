// Copyright (c) 2019 K Team. All Rights Reserved.

module LIST-IN-SYNTAX
    imports INT
    syntax Pgm ::= test ( Int )
endmodule

module LIST-IN
    imports LIST-IN-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> test( 1 ) => 3 in .List                                          ... </k>
    rule <k> test( 2 ) => 3 in ListItem ( 3 )                                 ... </k>
    rule <k> test( 3 ) => 4 in ListItem ( 3 )  ListItem ( 4 )  ListItem ( 5 ) ... </k>
    rule <k> test( 4 ) => 1 in ListItem ( 3 )  ListItem ( 4 )  ListItem ( 5 ) ... </k>
endmodule
