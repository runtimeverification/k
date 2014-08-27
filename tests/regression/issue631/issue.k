// Copyright (c) 2013-2014 K Team. All Rights Reserved.
/**
Verfies issue 631 found athttp://code.google.com/p/k-framework/issues/detail?id=631
Tests to see if list termiantion completion works with syntactic casting.
*/

module ISSUE
    syntax Ints ::= List{Int,","}
    syntax Exp ::= f(Ints)
    configuration
            <k> f( 1, .Ints ) </k>
            <out stream="stdout"> .List </out>

    // X must be of type Int to be completed with .Ints
    rule f(X::Int) => f(2) when X ==Int 1

    rule <k> f(2) => . </k>
        <out>... .List => ListItem(2) </out>

endmodule
