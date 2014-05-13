// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/set.k"

module TEST
imports SET
syntax KItem ::= "print"
configuration <k> print </k> <out> .MySet </out>
rule <k> print => .K ...</k> <out>... .MySet => MySetItem("foo") </out> [transition]
rule <k> print => .K ...</k> <out>... .MySet => MySetItem("bar") </out> [transition]
endmodule

