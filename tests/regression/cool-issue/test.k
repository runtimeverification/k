// Copyright (c) 2013-2014 K Team. All Rights Reserved.
module TEST
syntax KItem ::= "map" | "toMap"
configuration <k> $PGM:K </k>
rule map => toMap [supercool]
endmodule
