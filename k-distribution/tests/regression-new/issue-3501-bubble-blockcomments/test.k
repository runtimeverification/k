// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
    imports STRING-SYNTAX

    syntax Strings ::= List{String,","}
endmodule

module TEST
    imports TEST-SYNTAX
    rule/*1*/ "foo" => "bar"
    rule/*2*/ "bar" => "baz"

    rule "foo"/*1*/,"bar" => "baz"
endmodule
